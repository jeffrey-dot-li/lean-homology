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

/-! ### Chain-level cross product -/

/-- The cross product on singular chains, specialized to `ModuleCat R`:
  `crossProduct p q : C_p(X; R) ⊗ C_q(Y; R) → C_{p+q}(X × Y; R)`

Defined by distributing the tensor product over the coproducts (free module bases)
and applying the simplex-level cross product on each pair of generators.

In `ModuleCat R`, the coefficient module `Rmod R` is the monoidal unit `𝟙_ (ModuleCat R)`,
so `Rmod R ⊗ Rmod R ≅ Rmod R` via the left unitor — no separate `MonObj` instance is needed. -/
def crossProduct {X Y : TopCat.{u}} (p q : ℕ) :
    (mSingChain R X).X p ⊗ (mSingChain R Y).X q ⟶
      (mSingChain R (X ⨯ Y)).X (p + q) := by
  let A : SingularSimplex X p → ModuleCat.{u} R := fun _ => Rmod R
  let B : SingularSimplex Y q → ModuleCat.{u} R := fun _ => Rmod R
  -- Step 1: distribute ⊗ over left coproduct: (∐ A) ⊗ (∐ B) ≅ ∐_s (R ⊗ (∐ B))
  let leftIso :
      (∐ A) ⊗ (∐ B) ≅
        ∐ fun _s : SingularSimplex X p => (Rmod R) ⊗ (∐ B) :=
    PreservesCoproduct.iso (MonoidalCategory.tensorRight (∐ B)) A
  -- Step 2: distribute ⊗ over right coproduct: R ⊗ (∐ B) ≅ ∐_t (R ⊗ R)
  let rightIso :
        (Rmod R) ⊗ (∐ B) ≅
          ∐ fun _t : SingularSimplex Y q => (Rmod R) ⊗ (Rmod R) :=
    PreservesCoproduct.iso (MonoidalCategory.tensorLeft (Rmod R)) B
  exact
    leftIso.hom ≫
      Sigma.desc (fun s =>
        rightIso.hom ≫
          Sigma.desc (fun t =>
            -- Rmod R ⊗ Rmod R ⟶ chain group
            -- Since Rmod R = 𝟙_ (ModuleCat R), the left unitor gives R ⊗ R ≅ R
            (λ_ (Rmod R)).hom ≫
              simplexCrossProduct (R := Rmod R) s t
          )
      )

/-! ### Properties of the cross product -/

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
  sorry

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
