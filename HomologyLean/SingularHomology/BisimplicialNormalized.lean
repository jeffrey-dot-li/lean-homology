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

open AlgebraicTopology AlgebraicTopology.DoldKan CategoryTheory.Limits
open scoped Simplicial
open HomologyLean.SingularHomology

namespace CategoryTheory

namespace BisimplicialObject

variable {C : Type*} [Category* C] [Abelian C]

private lemma mooreInclusion_comp_mooreRetraction :
    mooreInclusion ≫ mooreRetraction = 𝟙 (normalizedMooreComplex C) := by
  ext Y : 2
  exact (splitMonoInclusionOfMooreComplexMap Y).id

/-- **Glue (split mono, lifted to the total complex).** The bi-normalized inclusion is a section
of the retraction. This lifts the Mathlib split-mono identity `(splitMonoInclusionOfMooreComplexMap
_).id` through `totalFunctor` in both simplicial directions. (Reused by `bridge₁`.) -/
@[reassoc]
lemma inclusionN₁_comp_retractionN₁ (X : BisimplicialObject C) :
    inclusionN₁ X ≫ retractionN₁ X = 𝟙 (N₁.obj X) := by
  dsimp only [inclusionN₁, retractionN₁]
  rw [← Functor.map_comp]
  refine Eq.trans (congrArg ((HomologicalComplex₂.totalFunctor _ _ _ _).map) ?_) <|
    (HomologicalComplex₂.totalFunctor _ _ _ _).map_id _
  let Y := ((alternatingFaceMapComplex (SimplicialObject C)).obj X)
  let M := (normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)
  have hBC :
      (NatTrans.mapHomologicalComplex mooreInclusion _).app Y ≫
          (NatTrans.mapHomologicalComplex mooreRetraction _).app Y =
        𝟙 (M.obj Y) := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
      mooreInclusion_comp_mooreRetraction, NatTrans.mapHomologicalComplex_id, NatTrans.id_app]
  calc
    (M.map (inclusionOfMooreComplexMap X) ≫
          (NatTrans.mapHomologicalComplex mooreInclusion _).app Y) ≫
        ((NatTrans.mapHomologicalComplex mooreRetraction _).app Y ≫
          M.map (PInftyToNormalizedMooreComplex X)) =
      M.map (inclusionOfMooreComplexMap X) ≫
          ((NatTrans.mapHomologicalComplex mooreInclusion _).app Y ≫
            (NatTrans.mapHomologicalComplex mooreRetraction _).app Y) ≫
        M.map (PInftyToNormalizedMooreComplex X) := by simp only [Category.assoc]
    _ = M.map (inclusionOfMooreComplexMap X) ≫ M.map (PInftyToNormalizedMooreComplex X) := by
      rw [hBC, Category.id_comp]
    _ = 𝟙 (M.obj ((normalizedMooreComplex (SimplicialObject C)).obj X)) := by
      rw [← M.map_comp]
      change M.map (inclusionOfMooreComplexMap X ≫
          (splitMonoInclusionOfMooreComplexMap X).retraction) = _
      rw [(splitMonoInclusionOfMooreComplexMap X).id, M.map_id]

/-- **(B) `∇` preserves normalization** (EM Lemma I.5.3). Precomposed with the bi-normalized
inclusion, the shuffle map already lands in the normalized diagonal, so the diagonal
renormalization round-trip `retractionN₂ ≫ inclusionN₂` (which equals `PInfty`) is a no-op.
`@[reassoc]` so it rewrites underneath the trailing `alexanderWhitney ≫ retractionN₁`. -/
@[reassoc]
lemma inclusionN₁_shuffleMap_diag_normalize (X : BisimplicialObject C) :
    inclusionN₁ X ≫ shuffleMap X ≫ retractionN₂ X ≫ inclusionN₂ X
      = inclusionN₁ X ≫ shuffleMap X := sorry

/-- **(A) EM `f∇ = i` modulo norms.** Unnormalized, `shuffleMap ≫ alexanderWhitney = 𝟙 + D` with
`D` landing in the degenerate subcomplex; the bi-normalized retraction `retractionN₁` annihilates
`D`, leaving `retractionN₁`. The combinatorial core is the shuffle pairing
`ezComponent ≫ awComponent` (diagonal `(r,s) = (p,q)` ↦ identity; off-diagonal ↦ degenerate). -/
lemma shuffleMap_alexanderWhitney_comp_retractionN₁ (X : BisimplicialObject C) :
    shuffleMap X ≫ alexanderWhitney X ≫ retractionN₁ X = retractionN₁ X := sorry

/-- **EM Thm 2.1a, first half (`f∇ = i`).** On normalized complexes the composite `∇ ≫ AW`
is the identity *strictly* — the degenerate cross-terms that obstruct this on the unnormalized
complex vanish modulo norms. -/
lemma normalizedShuffle_alexanderWhitney (X : BisimplicialObject C) :
    normalizedShuffleMap X ≫ normalizedAlexanderWhitney X = 𝟙 (N₁.obj X) := by
  simp only [normalizedShuffleMap, normalizedAlexanderWhitney, Category.assoc]
  rw [inclusionN₁_shuffleMap_diag_normalize_assoc,
    shuffleMap_alexanderWhitney_comp_retractionN₁, inclusionN₁_comp_retractionN₁]

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
