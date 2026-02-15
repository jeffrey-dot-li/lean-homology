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

/-! ### The canonical equivalence `R[A] ⊗ R[B] ≃ R[A × B]` -/

/-- The canonical `R`-linear equivalence between the tensor product of two free `R`-modules
(`∐ fun _ : A => R`) and the free module on the product (`∐ fun _ : A × B => R`).

This is `R[A] ⊗₍R₎ R[B] ≃ₗ[R] R[A × B]`, implemented by converting coproducts in `ModuleCat R`
to direct sums and using `TensorProduct.directSum`. -/
noncomputable def tensorCoprodEquiv (R : Type u) [CommRing R]
    (A B : Type u) [DecidableEq A] [DecidableEq B] :
    TensorProduct R (↑(∐ fun _ : A => (Rmod R))) (↑(∐ fun _ : B => (Rmod R))) ≃ₗ[R]
      ↑(∐ fun _ : A × B => (Rmod R)) := by
  classical
  let Z₁ : A → ModuleCat.{u} R := fun _ => Rmod R
  let Z₂ : B → ModuleCat.{u} R := fun _ => Rmod R
  let Z₁₂ : (A × B) → ModuleCat.{u} R := fun _ => Rmod R
  -- Work in direct sums of the underlying modules and then return to coproducts.
  refine (_root_.TensorProduct.congr
      (ModuleCat.coprodIsoDirectSum (Z := Z₁)).toLinearEquiv
      (ModuleCat.coprodIsoDirectSum (Z := Z₂)).toLinearEquiv) ≪≫ₗ ?_
  refine (TensorProduct.directSum (R := R) (S := R)
      (M₁ := fun _ : A => R) (M₂ := fun _ : B => R)) ≪≫ₗ ?_
  refine (DFinsupp.mapRange.linearEquiv (fun _ : A × B => (TensorProduct.lid R R))) ≪≫ₗ ?_
  exact (ModuleCat.coprodIsoDirectSum (Z := Z₁₂)).symm.toLinearEquiv

/-! ### Chain-level cross product -/

/-- The cross product on singular chains, specialized to `ModuleCat R`:
  `crossProduct p q : C_p(X; R) ⊗ C_q(Y; R) → C_{p+q}(X × Y; R)`

Defined via `TensorProduct.lift`: we construct the curried bilinear map
`C_p(X) →ₗ[R] (C_q(Y) →ₗ[R] C_{p+q}(X×Y))` using the coproduct (free module)
structure of the chain groups and the simplex-level cross product. -/
def crossProduct {X Y : TopCat.{u}} (p q : ℕ) :
    (mSingChain R X).X p ⊗ (mSingChain R Y).X q ⟶
      (mSingChain R (X ⨯ Y)).X (p + q) := by

  unfold mSingChain
  let αX := singChain_X_iso_sigma (C := ModuleCat.{u} R) (R := Rmod R) X p
  let αY := singChain_X_iso_sigma (C := ModuleCat.{u} R) (R := Rmod R) Y q
  let αXY := singChain_X_iso_sigma (C := ModuleCat.{u} R) (R := Rmod R) (X ⨯ Y) (p + q)
  refine ( (MonoidalCategory.tensorHom αX.hom αY.hom) ≫ ?_ ≫ αXY.inv)
  refine ModuleCat.ofHom ?_
  simp
  classical
  -- At this point the goal is a linear map out of a tensor product of two coproducts:
  -- `R[A] ⊗ R[B] →ₗ[R] R[...]`. We use the canonical linear equivalence
  -- `R[A] ⊗ R[B] ≃ₗ[R] R[A × B]` (free module on the product) to turn it into a map
  -- `R[A × B] →ₗ[R] ...`.
  let A : Type u := (stdSimplex.{u} p ⟶ X)
  let B : Type u := (stdSimplex.{u} q ⟶ Y)
  letI : DecidableEq A := Classical.decEq _
  letI : DecidableEq B := Classical.decEq _
  have e := tensorCoprodEquiv (R := R) A B
  -- Reduce the goal to a linear map `R[A × B] →ₗ[R] ...`.
  refine (?_ : (↑(∐ fun _ : A × B => Rmod R)) →ₗ[R] _).comp e.toLinearMap
  -- Now use the universal property of the free module:
  -- `R[A × B] →ₗ[R] M` is the same as `A × B → (the underlying type of M)`.
  letI : DecidableEq (A × B) := Classical.decEq _
  let isoDom :=
      (ModuleCat.coprodIsoDirectSum (Z := fun _ : A × B => Rmod R)).toLinearEquiv
  -- We don't introduce a separate `ab`; we define the generator map directly by uncurrying.
  -- For `s : A` and `t : B`, `simplexCrossProduct ⟪s⟫ₛ ⟪t⟫ₛ : R ⟶ C_{p+q}(X×Y)`; we then
  -- transport along `αXY.hom` to land in the reindexed coproduct.
  let onSimplices : A → B → _ :=
    fun s t =>
        ((simplexCrossProduct (R := Rmod R) (X := X) (Y := Y) (p := p) (q := q)
              ⟪s⟫ₛ ⟪t⟫ₛ))
  refine
      (DirectSum.toModule (R := R) (ι := A × B) (M := fun _ : A × B => R) (N := _)
            (fun ab =>
              -- A linear map `R →ₗ[R] M` is the same as a point of `M` (send `1` to that point).
              (LinearMap.ringLmapEquivSelf (R := R) (S := R) (M := _)).symm
                (αXY.hom ((onSimplices ab.1 ab.2) (1 : R))))).comp
        isoDom.toLinearMap



/-! ### Properties of the cross product -/

-- Naturality proof requires unfolding crossProduct and evaluating Sigma.desc on coprojections.
/-- **Naturality**: The cross product commutes with maps induced on chains.
For `f : X ⟶ X'` and `g : Y ⟶ Y'`, the following diagram commutes:
```
  C_p(X) ⊗ C_q(Y) --×--> C_{p+q}(X × Y)
       |                        |
  f_* ⊗ g_*                (f × g)_*
       |                        |
  C_p(X') ⊗ C_q(Y') --×--> C_{p+q}(X' × Y')
```
-/
theorem crossProduct_natural {X X' Y Y' : TopCat.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') (p q : ℕ) :
    crossProduct (R := R) (X := X) (Y := Y) p q ≫
      ((mSCF R).map (prod.map f g)).f (p + q) =
    (((mSCF R).map f).f p ⊗ₘ
      ((mSCF R).map g).f q) ≫
    crossProduct (R := R) (X := X') (Y := Y') p q := by
  ext aprodb
  refine TensorProduct.induction_on aprodb ?hz ?ht ?ha
  · -- f 0 = g 0
    simp
  · -- f (a ⨂ b) = g ( a ⨂ b)
    intro x y



    simp


  · -- goal: f (u + v) = g (u + v)
    intro u v hu hv
    simp






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
