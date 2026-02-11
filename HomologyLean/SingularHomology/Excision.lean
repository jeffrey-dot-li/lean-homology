/-
  The Excision Axiom for singular homology.

  If closure(U) ⊆ interior(A) for subsets U ⊆ A ⊆ X, then the inclusion
  (X \ U, A \ U) ↪ (X, A) induces isomorphisms on relative homology:
    H_n(X \ U, A \ U; R) ≅ H_n(X, A; R)

  The proof uses barycentric subdivision to make chains "small" relative
  to the open cover {A, X \ closure(U)}, then shows the inclusion of
  small chains is a quasi-isomorphism.

  This is the most technically demanding of the Eilenberg-Steenrod axioms.
  The main ingredients are:
  1. Barycentric subdivision Sd : C_*(X) → C_*(X), a chain map
  2. A chain homotopy T between Sd and id
  3. The smallness theorem: iterated Sd makes chains U-small
     (uses the Lebesgue number lemma for the compact simplex Δⁿ)
  4. The quasi-isomorphism from small chains to all chains
-/
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import HomologyLean.SingularHomology.Relative
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Topology.Basic

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe u v

variable (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts C]

namespace HomologyLean.SingularHomology

/-! ## Subspace inclusions as TopCat morphisms -/

/-- The continuous inclusion of a subset into the ambient space. -/
def subsetInclusion {X : TopCat.{v}} (A : Set X) : TopCat.of A ⟶ X :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The continuous inclusion of a subset into a larger subset. -/
def subsetInclusionSub {X : TopCat.{v}} {A B : Set X} (h : A ⊆ B) :
    TopCat.of A ⟶ TopCat.of B :=
  ⟨Set.inclusion h, continuous_inclusion h⟩

/-- Subspace inclusions are mono in TopCat (since Subtype.val is injective). -/
instance subsetInclusion_mono {X : TopCat.{v}} (A : Set X) :
    Mono (subsetInclusion A) := by
  sorry

/-- Inclusions between subsets are mono in TopCat. -/
instance subsetInclusionSub_mono {X : TopCat.{v}} {A B : Set X} (h : A ⊆ B) :
    Mono (subsetInclusionSub h) := by
  sorry

/-- Composing a subset inclusion with the ambient inclusion gives the
subset's own inclusion into the ambient space. -/
theorem subsetInclusionSub_comp {X : TopCat.{v}} {A B : Set X} (h : A ⊆ B) :
    subsetInclusionSub h ≫ subsetInclusion B = subsetInclusion A := by
  sorry

/-! ## Barycentric subdivision

Barycentric subdivision is a natural chain endomorphism `Sd : C_*(X) → C_*(X)`
that is chain homotopic to the identity. Each n-simplex σ : Δⁿ → X is
replaced by (n+1)! smaller simplices, obtained by composing σ with the
affine maps from the barycentric subdivision of the standard simplex Δⁿ.

The key property is that iterated barycentric subdivision makes all simplices
arbitrarily small: for any open cover of X, sufficiently many iterations
of Sd ensure each simplex in the subdivided chain has image in some element
of the cover (by the Lebesgue number lemma applied to the compact Δⁿ). -/

/-- The barycentric subdivision operator on singular chains.

For each n, `Sd` maps each singular n-simplex `σ : Δⁿ → X` to the formal sum
of (n+1)! singular n-simplices obtained by composing σ with the affine maps
from the barycentric subdivision of Δⁿ.

**Definition** (sorry'd): The subdivision is defined inductively on dimension,
using the cone construction. For n = 0, Sd is the identity. For n > 0,
Sd(σ) = b_σ * Sd(∂σ) where b_σ is the barycenter of σ and * denotes the
cone operator. -/
def barycentricSubdivision (R : C) (X : TopCat.{v}) :
    singularChains C R X ⟶ singularChains C R X := by
  sorry

/-- Barycentric subdivision is chain homotopic to the identity.

The chain homotopy `T` satisfies `∂T + T∂ = Sd - id`, which implies that
Sd induces the identity map on homology. The chain homotopy is constructed
by the acyclic models method (or an explicit inductive construction using
the cone operator on the contractible spaces Δⁿ). -/
def barycentricSubdivision_homotopic_id (R : C) (X : TopCat.{v}) :
    Homotopy (barycentricSubdivision C R X) (𝟙 (singularChains C R X)) := by
  sorry

/-- Barycentric subdivision is natural: for any `f : X ⟶ Y`,
`Sd ∘ C_*(f) = C_*(f) ∘ Sd`. -/
theorem barycentricSubdivision_natural (R : C) {X Y : TopCat.{v}} (f : X ⟶ Y) :
    singularChainMap C R f ≫ barycentricSubdivision C R Y =
      barycentricSubdivision C R X ≫ singularChainMap C R f := by
  sorry

/-! ## The excision theorem

The full proof of excision requires:
1. Defining the subcomplex of U-small chains for an open cover U of X
2. Showing iterated Sd lands in this subcomplex (Lebesgue number lemma)
3. Showing the inclusion of small chains is a quasi-isomorphism
4. Identifying the small chain complex for the cover {A, X \ closure U}
   with the chain complex of (X \ U, A \ U)

Steps 1-3 are substantial and will require additional helper definitions
during the fill-sorry phase. The excision theorem itself is stated below. -/

/-- The excision theorem for singular homology.

If `U ⊆ A ⊆ X` with `closure U ⊆ interior A`, then the inclusion
`(X \ U, A \ U) ↪ (X, A)` induces isomorphisms on relative homology:
  `H_n(X \ U, A \ U; R) ≅ H_n(X, A; R)` for all n.

Here, `X \ U = Uᶜ` is the complement of U in X, and `A \ U` is the
set difference. The inclusion of pairs is given by:
- `Uᶜ ↪ X` (complement inclusion)
- `A \ U ↪ Uᶜ` (since `A \ U ⊆ Uᶜ`)

**Proof sketch** (sorry'd): Use the cover `{A, X \ closure U}` of X.
Since `closure U ⊆ interior A`, the two sets cover X. Barycentric
subdivision makes chains small for this cover. The small chain complex
for this cover relative to A identifies with the chain complex of
(X \ U, A \ U), giving the excision isomorphism. -/
def excision (R : C) {X : TopCat.{v}} (A U : Set X)
    (hUA : U ⊆ A) (hsmall : closure U ⊆ interior A) (n : ℕ) :
    relativeSingularHomology C n R
      (subsetInclusionSub (show A \ U ⊆ Uᶜ from fun _ hx => hx.2)) ≅
    relativeSingularHomology C n R (subsetInclusion A) := by
  sorry

end HomologyLean.SingularHomology
