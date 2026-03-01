/-
  The homotopy map `X ⨯ Δ[1] ⟶ Y` and its endpoint evaluation lemmas.

  Given a topological homotopy `H : f ∼ g`, we construct a `TopCat` morphism
  `homotopyMap H : X ⨯ Δ[1] ⟶ Y` and show that composing with the two face
  inclusions `δ₀, δ₁ : Δ[0] → Δ[1]` recovers `f` and `g` respectively.
-/
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

noncomputable section

open CategoryTheory CategoryTheory.Limits unitInterval

universe u

namespace HomologyLean.SingularHomology

local notation "Δ[" p "]" => SimplexCategory.toTop.obj (SimplexCategory.mk p)

/-- The standard 1-simplex `Δ[1]` is isomorphic to the unit interval `I`. -/
noncomputable def stdSimplex1_iso_I : (Δ[1] : TopCat.{u}) ≅ TopCat.of (ULift.{u} I) := by
  refine TopCat.isoOfHomeo
    (Homeomorph.ulift.trans
      (stdSimplexHomeomorphUnitInterval.trans Homeomorph.ulift.symm))

/-- The homotopy map `Hmap : X ⨯ Δ[1] ⟶ Y` built from a topological homotopy
`H : f ∼ g` via braiding, the standard simplex–interval iso, and `H` itself. -/
noncomputable def homotopyMap {X Y : TopCat.{u}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom' g.hom') : X ⨯ Δ[1] ⟶ Y :=
  (prod.braiding X Δ[1]).hom ≫
    prod.map stdSimplex1_iso_I.hom (𝟙 X) ≫
    (TopCat.prodIsoProd _ X).hom ≫
    (show TopCat.of (ULift.{u} I × X) ⟶ Y from
      ⟨⟨fun ⟨t, x⟩ => H.toContinuousMap ⟨t.down, x⟩, by fun_prop⟩⟩)

/-- Composing a product simplex `(s, const ≫ δ₀)` with the homotopy map gives `s ≫ f`.

Geometrically: `δ₀` includes `Δ[0]` as vertex 1 of `Δ[1]`, which under the
standard simplex–interval homeomorphism corresponds to `t = 0` in `I`
(after the orientation reversal from `stdSimplexHomeomorphUnitInterval`),
so the homotopy evaluates to `f`. -/
lemma homotopyMap_comp_delta0 {X Y : TopCat.{u}} {n : ℕ} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom' g.hom') (s : Δ[n] ⟶ X) :
    prod.lift s (SimplexCategory.toTop.map default ≫
      SimplexCategory.toTop.map (SimplexCategory.δ 0)) ≫
    homotopyMap H = s ≫ f := by
  sorry

/-- Composing a product simplex `(s, const ≫ δ₁)` with the homotopy map gives `s ≫ g`.

Geometrically: `δ₁` includes `Δ[0]` as vertex 0 of `Δ[1]`, which under the
standard simplex–interval homeomorphism corresponds to `t = 1` in `I`,
so the homotopy evaluates to `g`. -/
lemma homotopyMap_comp_delta1 {X Y : TopCat.{u}} {n : ℕ} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom' g.hom') (s : Δ[n] ⟶ X) :
    prod.lift s (SimplexCategory.toTop.map default ≫
      SimplexCategory.toTop.map (SimplexCategory.δ 1)) ≫
    homotopyMap H = s ≫ g := by
  sorry

end HomologyLean.SingularHomology
