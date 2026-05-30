import HomologyLean.SingularHomology.BisimplicialNormalizedDefs

/-!
# Normalized Eilenberg–Zilber for bisimplicial objects

The literature (Eilenberg–Mac Lane II, Thm 2.1a) proves the Eilenberg–Zilber contraction on the
**normalized** complexes, where one direction is a strict identity and the other is a chain
homotopy via the explicit Eilenberg–Mac Lane homotopy. We assemble that here on the bi-normalized
total complex `N₁` and the normalized Moore complex of the diagonal `N₂` (both defined in
`BisimplicialNormalizedDefs.lean`).

The intended use is to transport this normalized equivalence to the unnormalized `F₁`/`F₂`
(in `Bisimplicial.lean`) along the Dold–Kan homotopy equivalence
`AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex`,
to obtain `eilenbergZilber : HomotopyEquiv (F₁.obj X) (F₂.obj X)`.

Everything here requires `[Abelian C]` (for the normalized Moore complex); the unnormalized
constructions in `Bisimplicial.lean` only need `[Preadditive C] [HasFiniteCoproducts C]`.
-/

open AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial
open HomologyLean.SingularHomology

namespace CategoryTheory

namespace BisimplicialObject

variable {C : Type*} [Category* C] [Abelian C]

/-- **EM Thm 2.1a, first half (`f∇ = i`).** On normalized complexes the composite `∇ ≫ AW`
is the identity *strictly* — the degenerate cross-terms that obstruct this on the unnormalized
complex vanish modulo norms. -/
lemma normalizedShuffle_alexanderWhitney (X : BisimplicialObject C) :
    normalizedShuffleMap X ≫ normalizedAlexanderWhitney X = 𝟙 (N₁.obj X) := sorry

/-- **EM Thm 2.1a, second half (`∂Φ + Φ∂ = ∇f − i`).** On normalized complexes the composite
`AW ≫ ∇` is chain homotopic to the identity via the Eilenberg–Mac Lane homotopy `Φ`. -/
noncomputable def homotopyNormalizedAlexanderWhitneyShuffle (X : BisimplicialObject C) :
    Homotopy (normalizedAlexanderWhitney X ≫ normalizedShuffleMap X) (𝟙 (N₂.obj X)) := sorry

/-- **Eilenberg–Zilber theorem on normalized complexes** (Eilenberg–Mac Lane II, Thm 2.1a).
The bi-normalized total complex is homotopy equivalent to the normalized Moore complex of the
diagonal. One direction is a strict identity; the other uses the EM homotopy. -/
noncomputable def eilenbergZilberNormalized (X : BisimplicialObject C) :
    HomotopyEquiv (N₁.obj X) (N₂.obj X) where
  hom := normalizedShuffleMap X
  inv := normalizedAlexanderWhitney X
  homotopyHomInvId := Homotopy.ofEq (normalizedShuffle_alexanderWhitney X)
  homotopyInvHomId := homotopyNormalizedAlexanderWhitneyShuffle X

end BisimplicialObject

end CategoryTheory
