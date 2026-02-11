/-
  The Dimension Axiom for singular homology.

  For a point (PUnit), we show:
  - H_n(pt; R) = 0 for n ≠ 0
  - H_0(pt; R) ≅ R

  This follows by specializing Mathlib's results for totally disconnected spaces
  to the one-point space.
-/
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe u v

variable (C : Type u) [Category.{v} C] [HasCoproducts C] [Preadditive C]
  [CategoryWithHomology C]

namespace HomologyLean.SingularHomology

/-- The one-point topological space, as an object of `TopCat`. -/
abbrev point : TopCat := TopCat.of PUnit

instance : TotallyDisconnectedSpace (point.carrier) := inferInstance

/-- H_n(pt; R) = 0 for n ≠ 0. This is the dimension axiom for higher degrees. -/
theorem singularHomology_point_isZero (R : C) (n : ℕ) (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor C n).obj R).obj point) :=
  isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R point hn

/-- H_0(pt; R) ≅ ∐ (fun _ : PUnit => R), the coproduct indexed by PUnit. -/
def singularHomology_point_zero_iso_sigma (R : C) :
    ((singularHomologyFunctor C 0).obj R).obj point ≅ ∐ fun _ : point => R :=
  singularHomologyFunctorZeroOfTotallyDisconnectedSpace C R point

/-- H_0(pt; R) ≅ R.
The coproduct over PUnit (a unique type) is isomorphic to R itself. -/
def singularHomology_point_zero_iso (R : C) :
    ((singularHomologyFunctor C 0).obj R).obj point ≅ R :=
  singularHomology_point_zero_iso_sigma C R ≪≫ coproductUniqueIso _

end HomologyLean.SingularHomology
