/-
  Cross product on singular chains — specialized to ModuleCat R.

  This file defines the chain-level cross product and proves homotopy invariance
  of singular homology, working concretely in `ModuleCat R` for a commutative ring `R`
  rather than in a general closed monoidal category.

  Key definitions:
  - `crossProduct p q` : the bilinear cross product C_p(X;R) ⊗ C_q(Y;R) → C_{p+q}(X×Y;R)

  Key results:
  - `crossProduct_natural` : naturality of the cross product
  - `crossProduct_leibniz` : Leibniz rule (chain map condition)
  - `crossProduct_normalized` : normalization on 0-simplices
  - `singularChain_chainHomotopy_of_homotopy` : chain homotopy from topological homotopy
  - `singularHomology_map_eq_of_homotopy` : homotopy invariance
  - `singularHomology_iso_of_homotopyEquiv` : homotopy equivalences induce isomorphisms
-/
import HomologyLean.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes


section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology unitInterval
open scoped MonoidalCategory

universe u

namespace HomologyLean.SingularHomology

variable (R : Type u) [CommRing R]

noncomputable section ModuleCatLemmas

/-! ### Pure `ModuleCat R` facts (no singular chains / simplices) -/

/-- The coefficient module: `R` viewed as an `R`-module.
In `ModuleCat R`, this is the monoidal unit `𝟙_ (ModuleCat R)`. -/
abbrev Rmod : ModuleCat.{u} R := ModuleCat.of R R

/-- Extensionality for morphisms out of a tensor of free `R`-modules: two morphisms
`f g : (∐_A R) ⊗ (∐_B R) ⟶ M` are equal if they agree when precomposed with
`Sigma.ι a ⊗ₘ Sigma.ι b` for all `a : A` and `b : B`. -/
lemma coprod_tensor_ext {A B : Type u} {M : ModuleCat.{u} R}
    {f g : (∐ fun _ : A => Rmod R) ⊗ (∐ fun _ : B => Rmod R) ⟶ M}
    (h : ∀ (a : A) (b : B),
      (Sigma.ι (fun _ : A => Rmod R) a ⊗ₘ Sigma.ι (fun _ : B => Rmod R) b) ≫ f =
      (Sigma.ι (fun _ : A => Rmod R) a ⊗ₘ Sigma.ι (fun _ : B => Rmod R) b) ≫ g) :
    f = g := by
  sorry

/-! ### Bridge between coproduct-based and Finsupp-based free modules -/

/-- The canonical isomorphism `∐ (fun _ : A => R) ≅ Free(A)` in `ModuleCat R`,
bridging the coproduct-based free module with the Finsupp-based one (`ModuleCat.free R`).

Constructed by composing `coprodIsoDirectSum` (coproduct → direct sum) with
`finsuppLEquivDirectSum.symm` (direct sum → Finsupp). -/
noncomputable def coprodIsoFree (R : Type u) [CommRing R] (A : Type u) :
    (∐ fun _ : A => Rmod R) ≅ (ModuleCat.free R).obj A := by
  classical
  exact ModuleCat.coprodIsoDirectSum (fun _ : A => Rmod R) ≪≫
    LinearEquiv.toModuleIso (finsuppLEquivDirectSum R R A).symm

/-- The natural isomorphism between the coproduct-based free module functor and
Mathlib's Finsupp-based `ModuleCat.free R`. Each component is `coprodIsoFree`. -/
noncomputable def coprodIsoFreeNat (R : Type u) [CommRing R] :
    coprodFreeFunctor (R := Rmod R) ≅ ModuleCat.free R :=
  NatIso.ofComponents
    (fun A => coprodIsoFree R A)
    (fun {A B} f => by sorry)

/-! ### The canonical isomorphism `Free(A) ⊗ Free(B) ≅ Free(A × B)` -/

/-- The isomorphism `Free(A) ⊗ Free(B) ≅ Free(A × B)` in `ModuleCat R`, expressing
that the free module functor is monoidal w.r.t. `(Type, ×)` and `(ModuleCat R, ⊗)`.

Built from `finsuppTensorFinsupp'` which gives `(A →₀ R) ⊗ (B →₀ R) ≃ₗ (A × B →₀ R)`. -/
noncomputable def freeTensorProductIso (R : Type u) [CommRing R]
    (A B : Type u) :
    ((ModuleCat.free R).obj A ⊗ (ModuleCat.free R).obj B) ≅
      (ModuleCat.free R).obj (A × B) :=
  LinearEquiv.toModuleIso (finsuppTensorFinsupp' R A B)

/-- Coproduct injection composed with `coprodIsoFree` maps `1 : R` to the
adjunction unit (= `Finsupp.single a 1`), i.e., the basis element in the
Finsupp-based free module. -/
lemma coprodIsoFree_ι (A : Type u) (a : A) :
    (ModuleCat.Hom.hom ((Sigma.ι (fun _ : A => Rmod R) a) ≫ (coprodIsoFree R A).hom))
      (1 : R) =
    (ModuleCat.adj R).unit.app A a := by
  sorry

/-- The monoidal structure iso `Free(A) ⊗ Free(B) ≅ Free(A × B)` maps
`η(a) ⊗ η(b)` to `η(a, b)` (basis element of the product). -/
lemma freeTensorProductIso_unit (A B : Type u) (a : A) (b : B) :
    (ModuleCat.Hom.hom (freeTensorProductIso R A B).hom)
      (TensorProduct.tmul R
        ((ModuleCat.adj R).unit.app A a)
        ((ModuleCat.adj R).unit.app B b)) =
    (ModuleCat.adj R).unit.app (A × B) (a, b) := by
  sorry

end ModuleCatLemmas

/-! ### Singular chains and simplices in `ModuleCat R` -/

/-- The singular chain functor with `R`-module coefficients. -/
noncomputable abbrev mSCF : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  SCF (C := ModuleCat.{u} R) (Rmod R)

/-- The singular chain complex of `X` with `R`-module coefficients. -/
noncomputable abbrev mSingChain (X : TopCat.{u}) : ChainComplex (ModuleCat.{u} R) ℕ :=
  singChain (C := ModuleCat.{u} R) (R := Rmod R) X

variable {R}

/-- The coprojection (basis inclusion) for a singular simplex, specialized to `ModuleCat R`. -/
noncomputable abbrev mι {X : TopCat.{u}} {n : ℕ} (s : SingularSimplex X n) :
    Rmod R ⟶ (mSingChain R X).X n :=
  simplexCoprojection (C := ModuleCat.{u} R) (R := Rmod R) s

/-- Factoring a coprojection through the identity simplex: `mι s` equals
`mι ⟪𝟙 Δ[n]⟫ₛ` composed with the chain map induced by `s.down`. -/
lemma mι_factor {X : TopCat.{u}} {n : ℕ} (s : SingularSimplex X n) :
    mι s = mι (⟪𝟙 Δ[n]⟫ₛ : SingularSimplex Δ[n] n) ≫ ((mSCF R).map s.down).f n := by
  sorry

/-! ### Naturality of `simplexCrossProduct` (specialized to `ModuleCat R`) -/

/-- The underlying element of the chain group corresponding to the simplex-level cross product,
obtained by evaluating the morphism `Rmod R ⟶ C_{p+q}(X×Y;R)` at `1 : R`. -/
noncomputable def simplexCrossProductElem {X Y : TopCat.{u}} {p q : ℕ}
    (s : SingularSimplex X p) (t : SingularSimplex Y q) :
    ↑((mSingChain R (X ⨯ Y)).X (p + q)) :=
  (simplexCrossProduct (R := Rmod R) (X := X) (Y := Y) (p := p) (q := q) s t) (1 : R)

/-- **Naturality** of `simplexCrossProductElem` in both variables. This is exactly the statement
that the assignment `(s,t) ↦ simplexCrossProductElem s t` is natural, as a function into the
underlying type of the chain group. -/
lemma simplexCrossProductElem_natural {X X' Y Y' : TopCat.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') (p q : ℕ)
    (s : SingularSimplex X p) (t : SingularSimplex Y q) :
    (ConcreteCategory.hom (((mSCF R).map (prod.map f g)).f (p + q)))
        (simplexCrossProductElem (R := R) (p := p) (q := q) s t)
      =
    simplexCrossProductElem (R := R) (p := p) (q := q) (⟪s.down ≫ f⟫ₛ) (⟪t.down ≫ g⟫ₛ) := by
  classical
  letI : CategoryTheory.MonObj (Rmod R) := by
    simpa [Rmod] using (inferInstance : CategoryTheory.MonObj (𝟙_ (ModuleCat.{u} R)))
  -- Reduce to the already-proved simplex-level naturality lemma in `HomotopyInvariance.lean`.
  cases s with
  | up s =>
    cases t with
    | up t =>
      -- `crossProduct_natural_pure_tensor` is a morphism-level naturality statement.
      -- Apply both sides to `1 : R` to get an elementwise statement.
      simpa [simplexCrossProductElem, mSCF, Category.assoc] using
        congrArg (fun k => (ModuleCat.Hom.hom k) (1 : R))
          (crossProduct_natural_pure_tensor
            (C := ModuleCat.{u} R) (R := Rmod R)
            (f := f) (g := g) (p := p) (q := q) (s := s) (t := t))

/-! ### `NatTrans` packaging of simplex-level naturality -/



/-- The degreewise chain group functor `mSCF R ⋙ eval p` is naturally isomorphic to
`singularSimplexFunctor p ⋙ ModuleCat.free R` (Finsupp-based free modules).

Composed from `chainGroupIsoCoprodFree` (coproduct = coproduct) and
`coprodIsoFreeNat` (coproduct ≅ Finsupp). -/
noncomputable def chainGroupIsoFree (p : ℕ) :
    mSCF R ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) p ≅
      singularSimplexFunctor p ⋙ ModuleCat.free R :=
  chainGroupIsoCoprodFree (R := Rmod R) p ≪≫
    Functor.isoWhiskerLeft (singularSimplexFunctor p) (coprodIsoFreeNat R)

/-- Functor `(TopCat × TopCat) ⥤ Type` sending `(X,Y)` to pairs of simplices
`SingularSimplex X p × SingularSimplex Y q`. -/
noncomputable def singularSimplexPairFunctor (p q : ℕ) : (TopCat.{u} × TopCat.{u}) ⥤ Type u :=
  (singularSimplexFunctor p).prod (singularSimplexFunctor q) ⋙
    Functor.uncurry.obj Types.binaryProductFunctor

/-- Target functor for the chain-level cross product (degreewise): `(X,Y) ↦ C_n(X×Y)`.

Defined as a functor composition:
`(TopCat × TopCat) ⥤ TopCat` (binary product) then `mSCF R` then `eval n`. -/
noncomputable abbrev crossProductTgtFunctor (n : ℕ) :
    (TopCat.{u} × TopCat.{u}) ⥤ ModuleCat.{u} R :=
  Functor.uncurry.obj (prod.functor : TopCat.{u} ⥤ TopCat.{u} ⥤ TopCat.{u}) ⋙
    mSCF R ⋙
      HomologicalComplex.eval (V := ModuleCat.{u} R) (c := ComplexShape.down ℕ) n

@[simp] lemma crossProductTgtFunctor_obj (n) (X Y) :
  (crossProductTgtFunctor (R:=R) n).obj (X,Y)
    = (mSingChain R (X ⨯ Y)).X n := rfl


/-- Functor `(TopCat × TopCat) ⥤ Type` sending `(X,Y)` to the underlying type of the chain group
`C_n(X×Y;R)` in `ModuleCat R`. Defined as `crossProductTgtFunctor ⋙ forget` so that
naturality statements involving both functors are definitionally compatible. -/
noncomputable abbrev chainGroupOnProdFunctor (R : Type u) [CommRing R] (n : ℕ) :
    (TopCat.{u} × TopCat.{u}) ⥤ Type u :=
  crossProductTgtFunctor (R := R) n ⋙ forget (ModuleCat.{u} R)

/-- `simplexCrossProduct` (specialized to `ModuleCat R`, evaluated at `1 : R`) as a natural
transformation
`(X,Y) ↦ SingularSimplex X p × SingularSimplex Y q ⟶ (forgetful type of C_{p+q}(X×Y;R))`. -/
noncomputable def simplexCrossProductNat (p q : ℕ) :
    singularSimplexPairFunctor (p := p) (q := q) ⟶ chainGroupOnProdFunctor (R := R) (p + q) where
  app XY st := simplexCrossProductElem (R := R) (p := p) (q := q) st.1 st.2
  naturality := by
    intro XY XY' fg
    funext st
    rcases st with ⟨s, t⟩
    -- This is exactly `simplexCrossProductElem_natural`.
    simpa [singularSimplexPairFunctor, chainGroupOnProdFunctor] using
      (simplexCrossProductElem_natural (R := R) (f := fg.1) (g := fg.2) (p := p) (q := q) s t).symm

/-! ### Chain-level cross product -/

/-- Source functor for the chain-level cross product (degreewise): `(X,Y) ↦ C_p(X) ⊗ C_q(Y)`. -/
noncomputable abbrev crossProductSrcFunctor (p q : ℕ) :
    (TopCat.{u} × TopCat.{u}) ⥤ ModuleCat.{u} R :=
  (mSCF R ⋙ HomologicalComplex.eval (V := ModuleCat.{u} R) (c := ComplexShape.down ℕ) p).prod
    (mSCF R ⋙ HomologicalComplex.eval (V := ModuleCat.{u} R) (c := ComplexShape.down ℕ) q) ⋙
    MonoidalCategory.tensor (C := ModuleCat.{u} R)

/-- Intermediate functor: `(X,Y) ↦ Free(SingularSimplex X p × SingularSimplex Y q)`,
i.e., the free `R`-module on simplex pairs, implemented via `ModuleCat.free R`. -/
noncomputable abbrev freePairFunctor (p q : ℕ) : (TopCat.{u} × TopCat.{u}) ⥤ ModuleCat.{u} R :=
  singularSimplexPairFunctor (p := p) (q := q) ⋙ ModuleCat.free R


/-- Naturality of `freeTensorProductIso`: tensoring free-module maps then applying the iso
equals applying the iso then mapping over the product. -/
lemma freeTensorProductIso_natural {A A' B B' : Type u}
    (f : A → A') (g : B → B') :
    ((ModuleCat.free R).map f ⊗ₘ (ModuleCat.free R).map g) ≫
      (freeTensorProductIso R A' B').hom =
    (freeTensorProductIso R A B).hom ≫ (ModuleCat.free R).map (Prod.map f g) := by
  have := (Functor.Monoidal.μNatIso (ModuleCat.free R)).hom.naturality
    (show (A, B) ⟶ (A', B') from (f, g))
  simp only [Functor.Monoidal.μNatIso_hom_app] at this
  convert this using 1

/-- Natural isomorphism `C_p(X) ⊗ C_q(Y) ≅ Free(SingularSimplex X p × SingularSimplex Y q)`,
bridging the coproduct-based chain groups with the Finsupp-based free module.

Defined via `NatIso.ofComponents` so that `.hom.app (X,Y)` definitionally reduces to
`tensorIso (chainGroupIsoFree p).app X (chainGroupIsoFree q).app Y ≪≫ freeTensorProductIso`,
making element-level proofs clean. The functor-level alternative (composing
`isoWhiskerRight`, `NatIso.prod`, `Functor.Monoidal.μNatIso`, `Functor.associator`)
gives naturality for free but introduces identity morphisms from associators
that block `erw`/`simp` at the element level. -/
noncomputable def tensorCoprodNatIso (p q : ℕ) :
    crossProductSrcFunctor (R := R) p q ≅ freePairFunctor (R := R) p q :=
  NatIso.ofComponents
    (fun ⟨X, Y⟩ =>
      MonoidalCategory.tensorIso ((chainGroupIsoFree (R := R) p).app X)
        ((chainGroupIsoFree (R := R) q).app Y) ≪≫
      freeTensorProductIso R
        ((singularSimplexFunctor p).obj X)
        ((singularSimplexFunctor q).obj Y))
    (by
      intro ⟨X, Y⟩ ⟨X', Y'⟩ ⟨f, g⟩
      simp only [Iso.trans_hom, MonoidalCategory.tensorIso_hom]
      dsimp only [crossProductSrcFunctor, freePairFunctor, Functor.comp_map, Functor.prod_map]
      simp only [MonoidalCategory.tensor_map]
      rw [← Category.assoc (f := _ ⊗ₘ _) (g := _ ⊗ₘ _)]
      rw [MonoidalCategory.tensorHom_comp_tensorHom]
      simp only [← Functor.comp_map]
      have nat_p := (chainGroupIsoFree (R := R) p).hom.naturality f
      have nat_q := (chainGroupIsoFree (R := R) q).hom.naturality g
      erw [nat_p, nat_q]
      rw [← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc, Category.assoc]
      congr 1
      exact freeTensorProductIso_natural
        ((singularSimplexFunctor p).map f) ((singularSimplexFunctor q).map g))

/-- The lift of `simplexCrossProductNat` through the free/forgetful adjunction:
`Free(SingularSimplex X p × SingularSimplex Y q) ⟶ C_{p+q}(X×Y;R)`,
natural in `(X,Y)`. -/
noncomputable def liftedCrossProductNat (p q : ℕ) :
    singularSimplexPairFunctor (p := p) (q := q) ⋙ ModuleCat.free R ⟶
      crossProductTgtFunctor (R := R) (p + q) := by
  let adjEquiv := (Adjunction.whiskerRight (TopCat × TopCat) (ModuleCat.adj R)).homEquiv
    (singularSimplexPairFunctor (p := p) (q := q))
    (crossProductTgtFunctor (R := R) (p + q))
  refine adjEquiv.symm ?_
  exact simplexCrossProductNat (R := R) (p := p) (q := q)

/-- The chain-level cross product as a natural transformation.

Defined as the composition `tensorCoprodNatIso.hom ≫ liftedCrossProductNat`:
1. `tensorCoprodNatIso` : `C_p(X) ⊗ C_q(Y) ≅ Free(SingularSimplex X p × SingularSimplex Y q)`
2. `liftedCrossProductNat` : `Free(simplex pairs) ⟶ C_{p+q}(X×Y;R)`

Naturality is automatic as a composition of natural transformations. -/
noncomputable def crossProductNat (p q : ℕ) :
    crossProductSrcFunctor (R := R) p q ⟶ crossProductTgtFunctor (R := R) (p + q) :=
  (tensorCoprodNatIso (R := R) p q).hom ≫ liftedCrossProductNat (R := R) p q

/-- The cross product on singular chains, extracted from the natural transformation
`crossProductNat` at a given pair of spaces `(X, Y)`. -/
noncomputable abbrev crossProduct {X Y : TopCat.{u}} (p q : ℕ) :
    (mSingChain R X).X p ⊗ (mSingChain R Y).X q ⟶
      (mSingChain R (X ⨯ Y)).X (p + q) :=
  (crossProductNat (R := R) p q).app (X, Y)


/-- **Adjunction identity**: the cross product, precomposed with `tensorCoprodNatIso.inv`
to extract `liftedCrossProductNat`, satisfies `η ≫ U(f#) = f` where
`f# = tensorCoprodNatIso.inv ≫ crossProductNat` and `f = simplexCrossProductNat`. -/
lemma crossProductNat_unit (p q : ℕ) (X : TopCat.{u}) (Y : TopCat.{u}) :
    (ModuleCat.adj R).unit.app (SingularSimplex X p × SingularSimplex Y q) ≫
      (forget (ModuleCat.{u} R)).map (
        (tensorCoprodNatIso (R := R) p q).inv.app (X, Y) ≫
          (crossProduct (X:=X) (Y:=Y) p q)
        )
        =
    (simplexCrossProductNat (R := R) (p := p) (q := q)).app (X, Y) := by
  -- Unfold crossProductNat and cancel tensorCoprodNatIso.inv ≫ tensorCoprodNatIso.hom
  unfold crossProduct
  simp only [crossProductNat, NatTrans.comp_app, Iso.inv_hom_id_app_assoc]
  -- Now the goal is about liftedCrossProductNat; unfold and use adjunction identity
  unfold liftedCrossProductNat
  change (ModuleCat.adj (R := R)).unit.app _ ≫
    (forget (ModuleCat R)).map ((ModuleCat.free R).map
      ((simplexCrossProductNat (R := R) p q).app (X, Y))) ≫
    (forget (ModuleCat R)).map ((ModuleCat.adj (R := R)).counit.app
      ((crossProductTgtFunctor (R := R) (p + q)).obj (X, Y))) =
    (simplexCrossProductNat (R := R) p q).app (X, Y)
  rw [← Functor.comp_map (ModuleCat.free R) (forget (ModuleCat R)),
      ← Category.assoc,
      ← (ModuleCat.adj (R := R)).unit.naturality]
  ext st
  exact congrFun ((ModuleCat.adj (R := R)).right_triangle_components
    ((crossProductTgtFunctor (R := R) (p + q)).obj (X, Y)))
    ((simplexCrossProductNat (R := R) p q).app (X, Y) st)



/-- The pure tensor `ι_s(1) ⊗ ι_t(1)` in `C_p(X) ⊗ C_q(Y)`, when mapped through
`tensorCoprodNatIso` to `Free(SingularSimplex X p × SingularSimplex Y q)`,
equals the basis element `freeMk (s, t) = η(s, t)`. -/
lemma mι_tensor_tensorCoprodNatIso {X Y : TopCat.{u}} {p q : ℕ}
    (s : SingularSimplex X p) (t : SingularSimplex Y q) :
    (ModuleCat.Hom.hom ((tensorCoprodNatIso (R := R) p q).hom.app (X, Y)))
      ((ModuleCat.Hom.hom (mι s ⊗ₘ mι t))
        ((ModuleCat.Hom.hom (λ_ (Rmod R)).inv) (1 : R))) =
    (ModuleCat.adj R).unit.app (SingularSimplex X p × SingularSimplex Y q) (s, t) := by
  -- tensorCoprodNatIso is ofComponents, so .hom.app reduces directly
  simp only [tensorCoprodNatIso, NatIso.ofComponents_hom_app,
    Iso.trans_hom, MonoidalCategory.tensorIso_hom,
    ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  -- Reduce: (λ_ R).inv 1 = 1 ⊗ₜ 1, tensorHom distributes
  erw [ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul]
  -- Clean up ConcreteCategory.hom ↔ ModuleCat.Hom.hom and (1,1).i = 1
  change (ModuleCat.Hom.hom (freeTensorProductIso R _ _).hom)
    ((ModuleCat.Hom.hom ((chainGroupIsoFree (R := R) p).hom.app X))
      ((ModuleCat.Hom.hom (mι s)) (1 : R)) ⊗ₜ[R]
     (ModuleCat.Hom.hom ((chainGroupIsoFree (R := R) q).hom.app Y))
      ((ModuleCat.Hom.hom (mι t)) (1 : R))) = _
  -- chainGroupIsoFree = Iso.refl ≪≫ coprodIsoFreeNat, hom.app reduces to coprodIsoFree
  simp only [chainGroupIsoFree, Iso.trans_hom, NatTrans.comp_app,
    ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    chainGroupIsoCoprodFree, NatIso.ofComponents_hom_app,
    Iso.refl_hom, ModuleCat.hom_id,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    coprodIsoFreeNat, mι]
  erw [coprodIsoFree_ι R _ s, coprodIsoFree_ι R _ t]
  exact freeTensorProductIso_unit R _ _ s t

/-- Applying `crossProduct` to a pure tensor of basis elements gives `simplexCrossProduct`.
```
  R ⊗ R ──── mι s ⊗ₘ mι t ────▶ Cₚ(X) ⊗ Cᵧ(Y)
    │                                   │
    │ (λ_ R).hom                        │ crossProduct p q
    ▼                                   ▼
    R ── simplexCrossProduct s t ──▶ Cₚ₊ᵧ(X × Y)
```
Proof strategy: `mι s ⊗ₘ mι t` factors through `(λ_ R).hom` by R-linearity
(since both `mι s` and `mι t` are maps from the monoidal unit `R`), giving
an arrow `h : R ⟶ Cₚ(X) ⊗ Cᵧ(Y)` from bottom-left to top-right.
It then suffices to show the bottom-right triangle commutes:
`h ≫ crossProduct p q = simplexCrossProduct s t`. -/
@[simp] lemma mι_tensor_comp_crossProduct {X Y : TopCat.{u}} {p q : ℕ}
    (s : SingularSimplex X p) (t : SingularSimplex Y q) :
    ((mι s ⊗ₘ mι t) ≫ crossProduct p q :
      Rmod R ⊗ Rmod R ⟶ (mSingChain (R := R) (X ⨯ Y)).X (p + q)) =
    (λ_ (Rmod R)).hom ≫ simplexCrossProduct (C := ModuleCat.{u} R) (R := Rmod R) s t := by
  have h := congrArg (fun k => k (s, t)) (crossProductNat_unit (R:=R) p q X Y)

  -- Step 1: Factor mι s ⊗ₘ mι t = (λ_ R).hom ≫ ((λ_ R).inv ≫ (mι s ⊗ₘ mι t))
  rw [show mι s ⊗ₘ mι t = (λ_ (Rmod R)).hom ≫ ((λ_ (Rmod R)).inv ≫ (mι s ⊗ₘ mι t)) from
    by rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]]
  rw [Category.assoc]
  congr 1
  -- Step 2: Bottom-right triangle — suffices to compare underlying linear maps
  apply ModuleCat.hom_ext

  -- Both sides are linear maps R →ₗ[R] C_{p+q}(X×Y); suffices to check at 1 : R
  ext
  -- LHS: ((λ_ R).inv ≫ (mι s ⊗ₘ mι t) ≫ crossProduct)(x)
  -- Unfold crossProduct = tensorCoprodNatIso.hom ≫ liftedCrossProductNat
  simp only [crossProduct, crossProductNat, NatTrans.comp_app,
    ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  -- After tensorCoprodNatIso.hom, use the bridge lemma + crossProductNat_unit

  erw [mι_tensor_tensorCoprodNatIso (R := R) s t]
  -- Now LHS is U(liftedCrossProductNat)(η(s,t)); use crossProductNat_unit
  have h := congrFun (crossProductNat_unit (R := R) p q X Y) (s, t)
  simp only [crossProduct, crossProductNat, NatTrans.comp_app,
    Iso.inv_hom_id_app_assoc, types_comp_apply] at h
  exact h

/-- On identity simplices, `simplexCrossProduct` reduces to `universalSimplexCrossProduct`. -/
@[simp] lemma simplexCrossProduct_id (p q : ℕ) :
    simplexCrossProduct (C := ModuleCat.{u} R) (R := Rmod R) ⟪𝟙 Δ[p]⟫ₛ ⟪𝟙 Δ[q]⟫ₛ =
    universalSimplexCrossProduct p q := by
  simp only [simplexCrossProduct, SingularSimplex.ofΔ_down]
  erw [prod.map_id_id, CategoryTheory.Functor.map_id, Category.comp_id]

/-- **Element-level Leibniz rule**: The cross product is compatible
with the boundary operators, stated for the universal simplices.
```
  ∂(s × t) = (∂s) × t + (-1)^{p+1} · s × (∂t)
```
Stated with shifted indices `(p+1, q+1)` to avoid natural number subtraction. -/
theorem simplexCrossProduct_leibniz (p q : ℕ) :
    (mι ⟪𝟙 Δ[p + 1]⟫ₛ ⊗ₘ mι ⟪𝟙 Δ[q + 1]⟫ₛ) ≫
      crossProduct (p + 1) (q + 1) ≫
      (mSingChain R (Δ[p + 1] ⨯ Δ[q + 1])).d ((p + 1) + (q + 1)) (p + (q + 1)) =
    (mι ⟪𝟙 Δ[p + 1]⟫ₛ ⊗ₘ mι ⟪𝟙 Δ[q + 1]⟫ₛ) ≫
      (((mSingChain R Δ[p + 1]).d (p + 1) p ⊗ₘ
          𝟙 ((mSingChain R Δ[q + 1]).X (q + 1))) ≫
        crossProduct p (q + 1)) +
    ((-1 : ℤ) ^ (p + 1)) •
      ((mι ⟪𝟙 Δ[p + 1]⟫ₛ ⊗ₘ mι ⟪𝟙 Δ[q + 1]⟫ₛ) ≫
        (𝟙 ((mSingChain R Δ[p + 1]).X (p + 1)) ⊗ₘ
            (mSingChain R Δ[q + 1]).d (q + 1) q) ≫
          crossProduct (p + 1) q ≫
          eqToHom (congrArg (mSingChain R (Δ[p + 1] ⨯ Δ[q + 1])).X (by omega))) := by
  rw [← Category.assoc, mι_tensor_comp_crossProduct, Category.assoc]
  simp only [simplexCrossProduct_id]
  conv_rhs =>
    lhs -- first summand
    rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  conv_rhs =>
    rhs; rhs -- second summand inside smul
    rw [← Category.assoc (mι ⟪𝟙 Δ[p + 1]⟫ₛ ⊗ₘ mι ⟪𝟙 Δ[q + 1]⟫ₛ),
        MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]

  sorry

/-- Pushing a tensor of chain maps past a tensor of morphisms and then past `crossProduct`.
Given commutativity conditions `hα : f_* ≫ α₁ = α₂ ≫ f_*` and `hβ : g_* ≫ β₁ = β₂ ≫ g_*`,
we can push `(f_* ⊗ₘ g_*)` past `(α₁ ⊗ₘ β₁) ≫ crossProduct` using interchange + naturality. -/
lemma crossProduct_tensor_naturality
    {X₁ X₂ Y₁ Y₂ : TopCat.{u}} {f : X₁ ⟶ X₂} {g : Y₁ ⟶ Y₂}
    {p₁ p₂ q₁ q₂ : ℕ}
    {α₁ : (mSingChain R X₂).X p₁ ⟶ (mSingChain R X₂).X p₂}
    {β₁ : (mSingChain R Y₂).X q₁ ⟶ (mSingChain R Y₂).X q₂}
    {α₂ : (mSingChain R X₁).X p₁ ⟶ (mSingChain R X₁).X p₂}
    {β₂ : (mSingChain R Y₁).X q₁ ⟶ (mSingChain R Y₁).X q₂}
    (hα : ((mSCF R).map f).f p₁ ≫ α₁ = α₂ ≫ ((mSCF R).map f).f p₂)
    (hβ : ((mSCF R).map g).f q₁ ≫ β₁ = β₂ ≫ ((mSCF R).map g).f q₂) :
    (((mSCF R).map f).f p₁ ⊗ₘ ((mSCF R).map g).f q₁) ≫
      (α₁ ⊗ₘ β₁) ≫ crossProduct p₂ q₂ =
    (α₂ ⊗ₘ β₂) ≫ crossProduct p₂ q₂ ≫
      ((mSCF R).map (prod.map f g)).f (p₂ + q₂) := by
  rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, hα, hβ,
      ← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]
  congr 1
  simpa [crossProductSrcFunctor, crossProductTgtFunctor, crossProduct] using
    (crossProductNat (R := R) p₂ q₂).naturality
      (show (X₁, Y₁) ⟶ (X₂, Y₂) from (f, g))

/-- A chain map commutes with `eqToHom` induced by an index equality. -/
lemma chainMap_f_comp_eqToHom {C D : ChainComplex (ModuleCat.{u} R) ℕ}
    (f : C ⟶ D) {n m : ℕ} (h : n = m) :
    f.f n ≫ eqToHom (congrArg D.X h) = eqToHom (congrArg C.X h) ≫ f.f m := by
  subst h; simp

/-- **Leibniz rule** (chain map condition): The cross product is compatible
with the boundary operators.
```
  ∂(σ × τ) = (∂σ) × τ + (-1)^{p+1} · σ × (∂τ)
```
Stated with shifted indices `(p+1, q+1)` to avoid natural number subtraction. -/
theorem crossProduct_leibniz {X Y : TopCat.{u}} (p q : ℕ) :
    crossProduct (R := R) (X := X) (Y := Y) (p + 1) (q + 1) ≫
      (mSingChain R (X ⨯ Y)).d ((p + 1) + (q + 1)) (p + (q + 1)) =
    (((mSingChain R X).d (p + 1) p ⊗ₘ
        𝟙 ((mSingChain R Y).X (q + 1))) ≫
      crossProduct p (q + 1)) +
    ((-1 : ℤ) ^ (p + 1)) •
      ((𝟙 ((mSingChain R X).X (p + 1)) ⊗ₘ
          (mSingChain R Y).d (q + 1) q) ≫
        crossProduct (p + 1) q ≫
        eqToHom (congrArg (mSingChain R (X ⨯ Y)).X (by omega))) := by
  apply coprod_tensor_ext
  intro s t
  simp only [Preadditive.comp_add, Preadditive.comp_zsmul]
  -- Factor: mι s = mι ⟪𝟙 Δ[p+1]⟫ₛ ≫ (s.down)_* and similarly for t.
  have hs := mι_factor (R := R) s
  have ht := mι_factor (R := R) t
  rw [show Sigma.ι _ s = mι s from rfl, show Sigma.ι _ t = mι t from rfl,
      hs, ht, ← MonoidalCategory.tensorHom_comp_tensorHom]
  -- Now the tensor is (mι ⟪𝟙⟫ₛ ⊗ₘ mι ⟪𝟙⟫ₛ) ≫ (s.down_* ⊗ₘ t.down_*).
  -- Use naturality of crossProduct to push (s.down_* ⊗ₘ t.down_*) past crossProduct on LHS.
  have nat : (((mSCF R).map s.down).f (p + 1) ⊗ₘ ((mSCF R).map t.down).f (q + 1)) ≫
      crossProduct (p + 1) (q + 1) =
    crossProduct (p + 1) (q + 1) ≫
      ((mSCF R).map (prod.map s.down t.down)).f ((p + 1) + (q + 1)) := by
    simpa [crossProductSrcFunctor, crossProductTgtFunctor, crossProduct] using
      (crossProductNat (R := R) (p + 1) (q + 1)).naturality
        (show (Δ[p + 1], Δ[q + 1]) ⟶ (X, Y) from (s.down, t.down))
  rw [Category.assoc, reassoc_of% nat]
  -- Naturality for RHS summands: push (s.down_* ⊗ₘ t.down_*) past crossProduct
  have nat1 : (((mSCF R).map s.down).f (p + 1) ⊗ₘ ((mSCF R).map t.down).f (q + 1)) ≫
      ((mSingChain R X).d (p + 1) p ⊗ₘ 𝟙 ((mSingChain R Y).X (q + 1))) ≫
      crossProduct p (q + 1) =
    ((mSingChain R Δ[p + 1]).d (p + 1) p ⊗ₘ 𝟙 ((mSingChain R Δ[q + 1]).X (q + 1))) ≫
      crossProduct p (q + 1) ≫
      ((mSCF R).map (prod.map s.down t.down)).f (p + (q + 1)) :=
    crossProduct_tensor_naturality (R := R)
      (((mSCF R).map s.down).comm (p + 1) p)
      (by simp [Category.comp_id, Category.id_comp])
  have nat2 : (((mSCF R).map s.down).f (p + 1) ⊗ₘ ((mSCF R).map t.down).f (q + 1)) ≫
      (𝟙 ((mSingChain R X).X (p + 1)) ⊗ₘ (mSingChain R Y).d (q + 1) q) ≫
      crossProduct (p + 1) q ≫
      eqToHom (congrArg (mSingChain R (X ⨯ Y)).X (by omega)) =
    (𝟙 ((mSingChain R Δ[p + 1]).X (p + 1)) ⊗ₘ (mSingChain R Δ[q + 1]).d (q + 1) q) ≫
      crossProduct (p + 1) q ≫
      eqToHom (congrArg (mSingChain R (Δ[p + 1] ⨯ Δ[q + 1])).X (by omega)) ≫
      ((mSCF R).map (prod.map s.down t.down)).f (p + (q + 1)) := by
    have base := crossProduct_tensor_naturality (R := R) (f := s.down) (g := t.down)
      (p₁ := p + 1) (p₂ := p + 1) (q₁ := q + 1) (q₂ := q)
      (α₁ := 𝟙 _) (α₂ := 𝟙 _)
      (by simp [Category.comp_id, Category.id_comp])
      (((mSCF R).map t.down).comm (q + 1) q)
    rw [reassoc_of% base, chainMap_f_comp_eqToHom (R := R) _ (by omega)]; rfl
  simp only [Category.assoc]
  rw [nat1, nat2]
  -- Use chain map condition: commute (prod.map s.down t.down)_* past d on LHS
  have comm : ((mSCF R).map (prod.map s.down t.down)).f (p + 1 + (q + 1)) ≫
      (mSingChain R (X ⨯ Y)).d (p + 1 + (q + 1)) (p + (q + 1)) =
    (mSingChain R (Δ[p + 1] ⨯ Δ[q + 1])).d (p + 1 + (q + 1)) (p + (q + 1)) ≫
      ((mSCF R).map (prod.map s.down t.down)).f (p + (q + 1)) :=
    ((mSCF R).map (prod.map s.down t.down)).comm _ _
  rw [comm]
  -- Left-associate to expose (mι ⊗ₘ mι) ≫ crossProduct ≫ d_ΔΔ for simplexCrossProduct_leibniz
  conv_lhs => rhs; rw [← Category.assoc]
  conv_lhs => rw [← Category.assoc]
  erw [simplexCrossProduct_leibniz (R := R) p q]
  simp only [Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc]

/-- **Normalization**: On 0-simplices (points), the cross product sends
`[x] ⊗ [y]` to `[(x, y)]`. That is, the cross product of two point-simplices
is the point-simplex at the product point.

In `ModuleCat R`, the multiplication `R ⊗ R → R` is the left unitor
(since `Rmod R = 𝟙_ (ModuleCat R)`). -/
theorem crossProduct_normalized {X Y : TopCat.{u}}
    (x : SingularSimplex X 0) (y : SingularSimplex Y 0) :
    (mι x ⊗ₘ mι y) ≫ crossProduct 0 0 =
    (λ_ (Rmod R)).hom ≫ mι (prodSimplex x y) := by
  rw [mι_tensor_comp_crossProduct]
  congr 1
  simp only [simplexCrossProduct, universalSimplexCrossProduct,
    mι, simplexCoprojection, prodSimplex]
  -- There is a unique (0,0)-shuffle, so the sum collapses to a single term.
  have huniq : ∀ (μ : Shuffle 0 0),
      μ.1 = ⟨fun _ => (0, 0), fun _ _ _ => le_refl _⟩ := by
    intro μ; ext x
    · simp [Fin.eq_zero (μ.1 x).1]
    · simp [Fin.eq_zero (μ.1 x).2]
  have hsub : Subsingleton (Shuffle 0 0) :=
    ⟨fun μ ν => Subtype.ext (by rw [huniq μ, huniq ν])⟩
  let μ₀ : Shuffle 0 0 := ⟨⟨fun _ => (0, 0), fun _ _ _ => le_refl _⟩,
    fun _ _ _ => Fin.ext (by simp [Fin.eq_zero])⟩
  rw [Fintype.sum_subsingleton _ μ₀]
  have hsign : μ₀.sign = 1 := by simp [Shuffle.sign, Shuffle.invCount]
  rw [hsign, one_smul]
  -- Reduce through the coproduct structure to a simplex equality.
  simp only [SCF, singChain]
  erw [colimit.ι_desc]
  simp only [Cofan.mk_ι_app, Category.id_comp]
  congr 1
  simp only [Nat.add_zero, Functor.op_obj, SimplexCategory.toTop_obj,
    SimplexCategory.len_mk, Nat.reduceAdd, yoneda,
    Pi.id_apply, singularSimplexEquivΔ_symm_apply]
  -- `shuffleStdSimplexMap μ₀ = prod.lift 𝟙 𝟙` since [0] → [0] is unique.
  have hshuf : shuffleStdSimplexMap (p := 0) (q := 0) μ₀ =
      prod.lift (𝟙 _) (𝟙 _) := by
    simp only [shuffleStdSimplexMap]
    congr 1 <;>
      rw [SimplexCategory.hom_zero_zero (SimplexCategory.Hom.mk _),
        SimplexCategory.toTop.map_id]
  -- Reduce to `.down` equality, then rewrite and simplify.
  have hext : ∀ (a b : SingularSimplex (X ⨯ Y) (0 + 0)),
      a.down = b.down → a = b := by
    intro a b h; cases a; cases b; congr
  apply hext
  simp only [shuffleSimplex]
  dsimp [TopCat.toSSet, Presheaf.restrictedULiftYoneda]
  simp only [prod.map_id_id, Category.comp_id]
  rw [hshuf, prod.lift_map]
  simp only [Nat.add_zero, SimplexCategory.toTop_obj, SimplexCategory.len_mk, Nat.reduceAdd,
    Category.id_comp]

/-! ## Chain homotopy from the cross product -/

/-- A topological homotopy `H : f ∼ g` between continuous maps `f g : X → Y`
induces a chain homotopy between the chain maps `C_*(f)` and `C_*(g)`.

**Proof sketch**: Use the cross product with the unit interval. The homotopy
`H : I × X → Y` composed with the cross product `C_0(I) ⊗ C_n(X) → C_n(I × X)`
gives the chain homotopy operator, using the fundamental class of `I` as a
1-chain connecting the two endpoints. -/
def singularChain_chainHomotopy_of_homotopy {X Y : TopCat.{u}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom' g.hom') :
    Homotopy
      ((mSCF R).map f)
      ((mSCF R).map g) := by
  sorry

/-! ## Homotopy invariance of singular homology -/

/-- Homotopic maps induce equal maps on singular homology.

This follows from `singularChain_chainHomotopy_of_homotopy` via
`Homotopy.homologyMap_eq`. -/
theorem singularHomology_map_eq_of_homotopy {X Y : TopCat.{u}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom' g.hom') (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} R) n).obj (Rmod R)).map f =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj (Rmod R)).map g := by
  exact (singularChain_chainHomotopy_of_homotopy (R := R) H).homologyMap_eq n

/-! ## Homotopy equivalences induce isomorphisms -/

/-- Homotopy equivalent spaces have isomorphic singular homology.

**Proof sketch**: `H_n(f) ∘ H_n(g) = H_n(g ≫ f) = H_n(𝟙 Y) = 𝟙` by
homotopy invariance and functoriality, and similarly for the other composite. -/
noncomputable def singularHomology_iso_of_homotopyEquiv {X Y : TopCat.{u}}
    (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : ContinuousMap.Homotopy (f ≫ g : X ⟶ X).hom' (𝟙 X : X ⟶ X).hom')
    (hgf : ContinuousMap.Homotopy (g ≫ f : Y ⟶ Y).hom' (𝟙 Y : Y ⟶ Y).hom')
    (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} R) n).obj (Rmod R)).obj X ≅
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj (Rmod R)).obj Y where
  hom := ((singularHomologyFunctor (ModuleCat.{u} R) n).obj (Rmod R)).map f
  inv := ((singularHomologyFunctor (ModuleCat.{u} R) n).obj (Rmod R)).map g
  hom_inv_id := by
    rw [← Functor.map_comp,
        singularHomology_map_eq_of_homotopy (R := R) hfg n]; simp
  inv_hom_id := by
    rw [← Functor.map_comp,
        singularHomology_map_eq_of_homotopy (R := R) hgf n]; simp

end HomologyLean.SingularHomology

end
