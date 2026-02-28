/-
  The standard 1-simplex `Δ[1]` is isomorphic to the unit interval `I` as topological spaces.

  This isomorphism is used in the construction of the chain homotopy for homotopy invariance
  of singular homology (see `singularChain_chainHomotopy_of_homotopy` in CrossProduct.lean).
-/
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.UnitInterval

open CategoryTheory AlgebraicTopology unitInterval

universe u

namespace HomologyLean.SingularHomology

/-- The standard 1-simplex `Δ[1]` is isomorphic to the unit interval `I`. -/
noncomputable def stdSimplex1_iso_I :
    (SimplexCategory.toTop.obj (SimplexCategory.mk 1) : TopCat.{u}) ≅ TopCat.of (ULift.{u} I) := sorry

end HomologyLean.SingularHomology
