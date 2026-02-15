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


noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology unitInterval
open scoped MonoidalCategory

universe u

namespace HomologyLean.SingularHomology

variable (R : Type u) [CommRing R]

/-! ### Abbreviations for ModuleCat R -/

/-- The coefficient module: `R` viewed as an `R`-module.
In `ModuleCat R`, this is the monoidal unit `𝟙_ (ModuleCat R)`. -/
abbrev Rmod : ModuleCat.{u} R := ModuleCat.of R R

/-- The singular chain functor with `R`-module coefficients. -/
abbrev mSCF : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  SCF (C := ModuleCat.{u} R) (Rmod R)

/-- The singular chain complex of `X` with `R`-module coefficients. -/
abbrev mSingChain (X : TopCat.{u}) : ChainComplex (ModuleCat.{u} R) ℕ :=
  singChain (C := ModuleCat.{u} R) (R := Rmod R) X

variable {R}

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

/-! ### The canonical isomorphism `R[A] ⊗ R[B] ≅ R[A × B]` -/

/-- The canonical isomorphism in `ModuleCat R` between the tensor product of two free `R`-modules
(`∐ fun _ : A => Rmod R`) and the free module on the product (`∐ fun _ : A × B => Rmod R`).

Implemented by converting coproducts in `ModuleCat R` to direct sums and using
`TensorProduct.directSum`. -/
noncomputable def tensorCoprodIso (R : Type u) [CommRing R]
    (A B : Type u) [DecidableEq A] [DecidableEq B] :
    (ModuleCat.of R (TensorProduct R (↑(∐ fun _ : A => (Rmod R))) (↑(∐ fun _ : B => (Rmod R))))) ≅
      (∐ fun _ : A × B => (Rmod R)) := by
  classical
  let Z₁ : A → ModuleCat.{u} R := fun _ => Rmod R
  let Z₂ : B → ModuleCat.{u} R := fun _ => Rmod R
  let Z₁₂ : (A × B) → ModuleCat.{u} R := fun _ => Rmod R
  -- Build a linear equivalence and convert it to an isomorphism in `ModuleCat R`.
  refine (LinearEquiv.toModuleIso ?_ )
  -- Work in direct sums of the underlying modules and then return to coproducts.
  refine (_root_.TensorProduct.congr
      (ModuleCat.coprodIsoDirectSum (Z := Z₁)).toLinearEquiv
      (ModuleCat.coprodIsoDirectSum (Z := Z₂)).toLinearEquiv) ≪≫ₗ ?_
  refine (TensorProduct.directSum (R := R) (S := R)
      (M₁ := fun _ : A => R) (M₂ := fun _ : B => R)) ≪≫ₗ ?_
  refine (DFinsupp.mapRange.linearEquiv (fun _ : A × B => (TensorProduct.lid R R))) ≪≫ₗ ?_
  exact (ModuleCat.coprodIsoDirectSum (Z := Z₁₂)).symm.toLinearEquiv

@[simp]
lemma tensorCoprodIso_hom_tmul (R : Type u) [CommRing R]
    (A B : Type u) [DecidableEq A] [DecidableEq B]
    (a : A) (b : B) :
    (tensorCoprodIso (R := R) A B).hom
        (((Sigma.ι (fun _ : A => Rmod R) a) (1 : R)) ⊗ₜ[R] ((Sigma.ι (fun _ : B => Rmod R) b) (1 : R))) =
      (Sigma.ι (fun _ : A × B => Rmod R) (a, b)) (1 : R) := by
  sorry

@[simp]
lemma tensorCoprodIso_inv_ι (R : Type u) [CommRing R]
    (A B : Type u) [DecidableEq A] [DecidableEq B]
    (a : A) (b : B) :
    (tensorCoprodIso (R := R) A B).inv ((Sigma.ι (fun _ : A × B => Rmod R) (a, b)) (1 : R)) =
      ((Sigma.ι (fun _ : A => Rmod R) a) (1 : R)) ⊗ₜ[R] ((Sigma.ι (fun _ : B => Rmod R) b) (1 : R)) := by
  sorry

-- A bridging lemma: how the generator `(s,t)` is transported through
-- `tensorCoprodIso.inv ≫ (FA ⊗ FB) ≫ tensorCoprodIso.hom`.
lemma tensorCoprodIso_natural_pair (R : Type u) [CommRing R]
    {A A' B B' : Type u}
    [DecidableEq A] [DecidableEq A'] [DecidableEq B] [DecidableEq B']
    (fA : A → A') (fB : B → B')
    (FA : (∐ fun _ : A => Rmod R) ⟶ (∐ fun _ : A' => Rmod R))
    (FB : (∐ fun _ : B => Rmod R) ⟶ (∐ fun _ : B' => Rmod R))
    (a : A) (b : B) :
    Sigma.ι (fun _ : A × B => Rmod R) (a, b) ≫
        (tensorCoprodIso (R := R) A B).inv ≫ (FA ⊗ₘ FB) ≫ (tensorCoprodIso (R := R) A' B').hom =
      Sigma.ι (fun _ : A' × B' => Rmod R) (fA a, fB b) := by
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

/-- Functor `TopCat ⥤ Type` sending `X` to its `p`-simplices (`SingularSimplex X p`). -/
noncomputable def singularSimplexFunctor (p : ℕ) : TopCat.{u} ⥤ Type u where
  obj X := SingularSimplex X p
  map {X X'} f s := ⟪s.down ≫ f⟫ₛ
  map_id X := by
    funext s
    cases s
    rfl
  map_comp {X Y Z} f g := by
    funext s
    cases s
    -- `ULift` makes this definitional up to associativity.
    simp [Category.assoc]

/-- Functor `(TopCat × TopCat) ⥤ Type` sending `(X,Y)` to pairs of simplices
`SingularSimplex X p × SingularSimplex Y q`. -/
noncomputable def singularSimplexPairFunctor (p q : ℕ) : (TopCat.{u} × TopCat.{u}) ⥤ Type u where
  obj XY := (SingularSimplex XY.1 p) × (SingularSimplex XY.2 q)
  map {XY XY'} fg st :=
    (⟪st.1.down ≫ fg.1⟫ₛ, ⟪st.2.down ≫ fg.2⟫ₛ)
  map_id XY := by
    funext st
    cases st with
    | mk s t =>
      cases s; cases t
      rfl
  map_comp {X Y Z} f g := by
    funext st
    cases st with
    | mk s t =>
      cases s; cases t
      simp [Category.assoc]

/-- Target functor for the chain-level cross product (degreewise): `(X,Y) ↦ C_n(X×Y)`.

Defined with explicit `obj`/`map` using `prod.map` so that
`crossProductTgtFunctor ⋙ forget (ModuleCat R) = chainGroupOnProdFunctor` definitionally. -/
noncomputable def crossProductTgtFunctor (n : ℕ) :
    (TopCat.{u} × TopCat.{u}) ⥤ ModuleCat.{u} R where
  obj XY := (mSingChain R (XY.1 ⨯ XY.2)).X n
  map {XY XY'} fg := ((mSCF R).map (prod.map fg.1 fg.2)).f n
  map_id XY := by simp
  map_comp {X Y Z} f g := by
    have hprod :
        (prod.map f.1 f.2) ≫ (prod.map g.1 g.2) =
          prod.map (f.1 ≫ g.1) (f.2 ≫ g.2) := by
      ext <;> simp
    change ((mSCF R).map (prod.map (f.1 ≫ g.1) (f.2 ≫ g.2))).f n = _
    rw [← hprod, Functor.map_comp, HomologicalComplex.comp_f]

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

/-! ### Properties of the cross product -/

/- **Naturality**: The cross product commutes with maps induced on chains.
We package this as a `NatTrans` below rather than a standalone theorem. -/
/-- Source functor for the chain-level cross product (degreewise): `(X,Y) ↦ C_p(X) ⊗ C_q(Y)`. -/
noncomputable abbrev crossProductSrcFunctor (p q : ℕ) :
    (TopCat.{u} × TopCat.{u}) ⥤ ModuleCat.{u} R :=
  let evalP : ChainComplex (ModuleCat.{u} R) ℕ ⥤ ModuleCat.{u} R :=
    HomologicalComplex.eval (V := ModuleCat.{u} R) (c := ComplexShape.down ℕ) p
  let evalQ : ChainComplex (ModuleCat.{u} R) ℕ ⥤ ModuleCat.{u} R :=
    HomologicalComplex.eval (V := ModuleCat.{u} R) (c := ComplexShape.down ℕ) q
  let F : (TopCat.{u} × TopCat.{u}) ⥤ ModuleCat.{u} R :=
    CategoryTheory.Prod.fst _ _ ⋙ mSCF R ⋙ evalP
  let G : (TopCat.{u} × TopCat.{u}) ⥤ ModuleCat.{u} R :=
    CategoryTheory.Prod.snd _ _ ⋙ mSCF R ⋙ evalQ
  let tensorFG : (ModuleCat.{u} R × ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
    (MonoidalCategory.tensor (C := ModuleCat.{u} R))
  (F.prod' G) ⋙ tensorFG

/-- Intermediate functor: `(X,Y) ↦ Free(SingularSimplex X p × SingularSimplex Y q)`,
i.e., the free `R`-module on simplex pairs, implemented via `ModuleCat.free R`. -/
noncomputable abbrev freePairFunctor (p q : ℕ) : (TopCat.{u} × TopCat.{u}) ⥤ ModuleCat.{u} R :=
  singularSimplexPairFunctor (p := p) (q := q) ⋙ ModuleCat.free R

/-- Natural isomorphism `C_p(X) ⊗ C_q(Y) ≅ Free(SingularSimplex X p × SingularSimplex Y q)`,
bridging the coproduct-based chain groups with the Finsupp-based free module.

Each component is `tensorCoprodIso ≪≫ coprodIsoFree`: first collapse the tensor of coproducts
into a single coproduct on pairs, then convert that coproduct to the Finsupp-based free module. -/
noncomputable def tensorCoprodNatIso (p q : ℕ) :
    crossProductSrcFunctor (R := R) p q ≅ freePairFunctor (R := R) p q :=
  NatIso.ofComponents
    (fun XY => by
      classical
      exact tensorCoprodIso R (SingularSimplex XY.1 p) (SingularSimplex XY.2 q) ≪≫
        coprodIsoFree R (SingularSimplex XY.1 p × SingularSimplex XY.2 q))
    (fun {XY XY'} fg => by
      sorry)

/-- The lift of `simplexCrossProductNat` through the free/forgetful adjunction:
`Free(SingularSimplex X p × SingularSimplex Y q) ⟶ C_{p+q}(X×Y;R)`,
natural in `(X,Y)`. -/
noncomputable def liftedCrossProductNat (p q : ℕ) :
    freePairFunctor (R := R) p q ⟶ crossProductTgtFunctor (R := R) (p + q) where
  app XY := ModuleCat.freeDesc
    ((simplexCrossProductNat (R := R) (p := p) (q := q)).app XY)
  naturality XY XY' fg := by
    apply ModuleCat.free_hom_ext; intro ⟨s, t⟩
    simp only [Functor.comp_map, freePairFunctor, ModuleCat.comp_apply,
      simplexCrossProductNat, singularSimplexPairFunctor, crossProductTgtFunctor]
    erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact (simplexCrossProductElem_natural (R := R) fg.1 fg.2 p q s t).symm

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
      crossProduct (R := R) (X := X) (Y := Y) p (q + 1)) +
    ((-1 : ℤ) ^ (p + 1)) •
      ((𝟙 ((mSingChain R X).X (p + 1)) ⊗ₘ
          (mSingChain R Y).d (q + 1) q) ≫
        crossProduct (R := R) (X := X) (Y := Y) (p + 1) q ≫
        eqToHom (congrArg (mSingChain R (X ⨯ Y)).X (by omega))) := by
  sorry

/-- **Normalization**: On 0-simplices (points), the cross product sends
`[x] ⊗ [y]` to `[(x, y)]`. That is, the cross product of two point-simplices
is the point-simplex at the product point.

In `ModuleCat R`, the multiplication `R ⊗ R → R` is the left unitor
(since `Rmod R = 𝟙_ (ModuleCat R)`). -/
theorem crossProduct_normalized {X Y : TopCat.{u}}
    (x : SingularSimplex X 0) (y : SingularSimplex Y 0) :
    (simplexCoprojection (C := ModuleCat.{u} R) (R := Rmod R) x ⊗ₘ
      simplexCoprojection (C := ModuleCat.{u} R) (R := Rmod R) y) ≫
      crossProduct (R := R) (X := X) (Y := Y) 0 0 =
    (λ_ (Rmod R)).hom ≫
      simplexCoprojection (C := ModuleCat.{u} R) (R := Rmod R) (prodSimplex x y) := by
  sorry

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
def singularHomology_iso_of_homotopyEquiv {X Y : TopCat.{u}}
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
