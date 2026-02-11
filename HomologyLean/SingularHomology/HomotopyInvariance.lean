/-
  Homotopy Invariance of singular homology.

  Homotopic maps f, g : X → Y induce equal maps on singular homology:
    H_n(f) = H_n(g) : H_n(X; R) → H_n(Y; R)

  The proof uses the prism operator construction, which produces a chain
  homotopy between the chain maps C_*(f) and C_*(g) from a topological
  homotopy H : f ≃ g.

  Key construction:
  - The prism operator P_n : C_n(X) → C_{n+1}(X × I) decomposes Δⁿ × I
    into (n+1) simplices of dimension n+1, using the maps
      τᵢ : Δⁿ⁺¹ → Δⁿ × Δ¹,  vⱼ ↦ (vⱼ, 0) for j ≤ i, (vⱼ₋₁, 1) for j > i.
  - The boundary formula ∂P + P∂ = (i₁)_* - (i₀)_* makes P a chain homotopy
    between the chain maps induced by the inclusions at 0 and 1.
  - Composing with C_*(H) transforms P into a chain homotopy between
    C_*(f) and C_*(g).
-/
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Algebra.Homology.Homotopy

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe u v

variable (C : Type u) [Category.{v} C] [HasCoproducts C] [Preadditive C]
  [CategoryWithHomology C]

namespace HomologyLean.SingularHomology

/-! ## Chain homotopy from topological homotopy

The core construction: a topological homotopy `H : f ≃ g` induces a chain
homotopy between `C_*(f)` and `C_*(g)`. The chain homotopy data
`h_n : C_n(X; R) → C_{n+1}(Y; R)` is defined as the composition of the
prism operator `P_n : C_n(X) → C_{n+1}(X × I)` with `C_{n+1}(H)`.

The verification uses the boundary formula `∂P + P∂ = (i₁)_* - (i₀)_*`
together with `H ∘ i₀ = f` and `H ∘ i₁ = g`. -/

/-- A topological homotopy `H : f ≃ g` between continuous maps `f g : X → Y`
induces a chain homotopy between the chain maps `C_*(f)` and `C_*(g)`.

**Proof sketch** (sorry'd): Construct the prism operator
`P_n : C_n(X) → C_{n+1}(X × I)` from the standard triangulation of
`Δⁿ × I` into `(n+1)` simplices, then compose with `C_{n+1}(H)`.
The chain homotopy identity follows from `∂P + P∂ = (i₁)_* - (i₀)_*`. -/
def singularChain_chainHomotopy_of_homotopy {X Y : TopCat.{v}} {f g : X ⟶ Y}
    (R : C) (H : ContinuousMap.Homotopy f.hom' g.hom') :
    Homotopy
      (((singularChainComplexFunctor C).obj R).map f)
      (((singularChainComplexFunctor C).obj R).map g) := by
  sorry

/-! ## Homotopy invariance of singular homology -/

/-- Homotopic maps induce equal maps on singular homology.

This follows from `singularChain_chainHomotopy_of_homotopy` via
`Homotopy.homologyMap_eq`. -/
theorem singularHomology_map_eq_of_homotopy {X Y : TopCat.{v}} {f g : X ⟶ Y}
    (R : C) (H : ContinuousMap.Homotopy f.hom' g.hom') (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).map f =
      ((singularHomologyFunctor C n).obj R).map g := by
  sorry

/-! ## Homotopy equivalences induce isomorphisms -/

/-- Homotopy equivalent spaces have isomorphic singular homology.

**Proof sketch**: `H_n(f) ∘ H_n(g) = H_n(g ≫ f) = H_n(𝟙 Y) = 𝟙` by
homotopy invariance and functoriality, and similarly for the other composite. -/
def singularHomology_iso_of_homotopyEquiv {X Y : TopCat.{v}} (R : C)
    (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : ContinuousMap.Homotopy (f ≫ g : X ⟶ X).hom' (𝟙 X : X ⟶ X).hom')
    (hgf : ContinuousMap.Homotopy (g ≫ f : Y ⟶ Y).hom' (𝟙 Y : Y ⟶ Y).hom')
    (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).obj X ≅
      ((singularHomologyFunctor C n).obj R).obj Y := by
  sorry

end HomologyLean.SingularHomology
