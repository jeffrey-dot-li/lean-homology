import HomologyLean.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

open CategoryTheory CategoryTheory.Limits AlgebraicTopology unitInterval
open scoped MonoidalCategory

universe u v

namespace HomologyLean.SingularHomology

variable (R : Type u) [CommRing R]

/-! ### ModuleCat R setup (copied from CrossProduct) -/

/-- The coefficient module: `R` viewed as an `R`-module. -/
abbrev Rmod : ModuleCat.{u} R := ModuleCat.of R R

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

/-! ### boundary_identity_1simplex -/

namespace Working

variable {C : Type u} [Category.{v} C] [HasCoproducts C] [Preadditive C] [CategoryWithHomology C]
   [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
variable {R_C : C}


lemma simplexCrossProduct_zero_left {X Y : TopCat.{v}} {n : ℕ}
    (c : SingularSimplex X 0) (s : SingularSimplex Y n) :
    simplexCrossProduct (C := C) (R := R_C) c s =
    simplexCoprojection
      ⟪prod.lift (SimplexCategory.toTop.map default ≫ c.down) s.down⟫ₛ ≫
    eqToHom (by simp) := by
  sorry



-- Prototype: δ_cast_simplexProdMap proof
-- Goal: show (h ▸ ULift.up f).down = eqToHom _ ≫ f for toSSet elements

-- set_option maxHeartbeats 400000 in
lemma cast_ulift_down_eq {p q n : ℕ} (h : p + q = n + 1)
    (X : TopCat.{v})
    (f : stdSimplex.{v} (p + q) ⟶ X) :
    (show (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk (n + 1))) from
      h ▸ (ULift.up f : (TopCat.toSSet.obj X).obj
        (Opposite.op (SimplexCategory.mk (p + q))))).down =
    eqToHom (congrArg (SimplexCategory.toTop.obj ∘ SimplexCategory.mk) h.symm) ≫ f := by
  -- Generalize to eliminate the h ▸
  generalize hm : n + 1 = m at h ⊢
  revert f
  rcases h
  intro f
  simp

end Working

end HomologyLean.SingularHomology
