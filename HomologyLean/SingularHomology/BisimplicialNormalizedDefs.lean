import HomologyLean.SingularHomology.Bisimplicial
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.AlgebraicTopology.MooreComplex
import Mathlib.AlgebraicTopology.DoldKan.Normalized

/-!
# Normalized Eilenberg–Zilber: definitions

This file collects the **definitions** for the normalized Eilenberg–Zilber theorem (the proofs and
the assembled equivalence live in `BisimplicialNormalized.lean`).

We compare two `ChainComplex C ℕ`-valued functors on bisimplicial objects:

* `N₁` — the **bi-normalized total complex**: normalize both simplicial directions via the
  normalized Moore complex, then total.
* `N₂` — the **normalized Moore complex of the diagonal**.

## Map strategy (option 3: via `PInfty`)

Rather than writing explicit combinatorial formulas directly on the Moore *subobjects* (awkward,
since `normalizedMooreComplex` is an intersection-of-kernels subobject), or proving an explicit
contraction on the unnormalized complex (no literature support), we define the normalized maps by
**transporting the unnormalized `shuffleMap`/`alexanderWhitney` through the Dold–Kan
normalization**. Concretely, the maps factor through the idempotent `PInfty` on the unnormalized
(alternating-face-map) complex / the Moore inclusion–retraction pair. This keeps the maps
levelwise-concrete *and* makes the degenerate cross-terms vanish in the contraction proofs
(`PInfty` kills degeneracies), which is exactly the "modulo norms = 0" step in
Eilenberg–Mac Lane II, Thm 2.1a.

Everything here requires `[Abelian C]` (for the normalized Moore complex); the unnormalized
constructions in `Bisimplicial.lean` only need `[Preadditive C] [HasFiniteCoproducts C]`.
-/

open AlgebraicTopology AlgebraicTopology.DoldKan CategoryTheory.Limits
open scoped Simplicial
open HomologyLean.SingularHomology

namespace CategoryTheory

namespace BisimplicialObject

variable {C : Type*} [Category* C] [Abelian C]

-- `SimplicialObject C` is a `def`, so the functor-category `Abelian` instance is not found by
-- unfolding; provide it explicitly (needed for the outer `normalizedMooreComplex`).
noncomputable instance : Abelian (SimplicialObject C) :=
  CategoryTheory.Abelian.functorCategoryAbelian

-- TODO: `normalizedMooreComplex` is additive (the Moore differentials are induced by additive
-- face maps), but Mathlib has no instance and `cat_disch` can't discharge `map_add` through the
-- subobject factorization. Proved by `sorry` for now.
instance : (normalizedMooreComplex C).Additive where
  map_add := by
    intro X Y f g
    ext n
    cases n with
    | zero =>
        dsimp [normalizedMooreComplex, NormalizedMooreComplex.map]
        apply (cancel_mono ((⊤ : Subobject (Y.obj (Opposite.op ⦋0⦌))).arrow)).1
        rw [Preadditive.add_comp, Subobject.factorThru_arrow, Subobject.factorThru_arrow,
          Subobject.factorThru_arrow, NatTrans.app_add, Preadditive.comp_add]
    | succ n =>
        dsimp [normalizedMooreComplex, NormalizedMooreComplex.map]
        apply (cancel_mono
          ((Finset.univ.inf fun k : Fin (n + 1) => kernelSubobject (Y.δ k.succ)).arrow)).1
        rw [Preadditive.add_comp, Subobject.factorThru_arrow, Subobject.factorThru_arrow,
          Subobject.factorThru_arrow, NatTrans.app_add, Preadditive.comp_add]

/-- The **bi-normalized total complex**: normalize both simplicial directions (via the
normalized Moore complex), then take the total complex. The normalized analogue of `F₁`. -/
noncomputable abbrev N₁ : BisimplicialObject C ⥤ ChainComplex C ℕ :=
  normalizedMooreComplex _ ⋙
    (normalizedMooreComplex C).mapHomologicalComplex _ ⋙
      HomologicalComplex₂.totalFunctor _ _ _ _

/-- The **normalized Moore complex of the diagonal**. The normalized analogue of `F₂`. -/
noncomputable abbrev N₂ : BisimplicialObject C ⥤ ChainComplex C ℕ :=
  diag ⋙ normalizedMooreComplex C

/-- The Moore inclusion `N[-] ⟶ K[-]` packaged as a natural transformation. Needed to lift the
inner-direction normalization through `mapHomologicalComplex`. -/
noncomputable def mooreInclusion :
    normalizedMooreComplex C ⟶ alternatingFaceMapComplex C where
  app Y := inclusionOfMooreComplexMap Y
  naturality _ _ _ := by cat_disch

/-- The Dold–Kan retraction `K[-] ⟶ N[-]` (via `PInfty`) as a natural transformation. -/
noncomputable def mooreRetraction :
    alternatingFaceMapComplex C ⟶ normalizedMooreComplex C where
  app Y := PInftyToNormalizedMooreComplex Y
  naturality _ _ _ := by cat_disch

variable (X : BisimplicialObject C)

/-- Inclusion `N₁ ↪ F₁` of the bi-normalized total complex into the unnormalized total complex,
obtained by including both simplicial directions (`inclusionOfMooreComplexMap` outer,
`mooreInclusion` inner) and totalizing. -/
noncomputable def inclusionN₁ : N₁.obj X ⟶ F₁.obj X :=
  (HomologicalComplex₂.totalFunctor _ _ _ _).map
    (((normalizedMooreComplex C).mapHomologicalComplex _).map (inclusionOfMooreComplexMap X) ≫
      (NatTrans.mapHomologicalComplex mooreInclusion _).app
        ((alternatingFaceMapComplex (SimplicialObject C)).obj X))

/-- Retraction `F₁ ↠ N₁` onto the bi-normalized total complex (via `PInfty` in both directions). -/
noncomputable def retractionN₁ : F₁.obj X ⟶ N₁.obj X :=
  (HomologicalComplex₂.totalFunctor _ _ _ _).map
    ((NatTrans.mapHomologicalComplex mooreRetraction _).app
        ((alternatingFaceMapComplex (SimplicialObject C)).obj X) ≫
      ((normalizedMooreComplex C).mapHomologicalComplex _).map (PInftyToNormalizedMooreComplex X))

/-- Inclusion `N₂ ↪ F₂` for the diagonal (the Moore inclusion). -/
noncomputable def inclusionN₂ : N₂.obj X ⟶ F₂.obj X :=
  inclusionOfMooreComplexMap (diag.obj X)

/-- Retraction `F₂ ↠ N₂` for the diagonal (the `PInfty` retraction). -/
noncomputable def retractionN₂ : F₂.obj X ⟶ N₂.obj X :=
  PInftyToNormalizedMooreComplex (diag.obj X)

/-- The shuffle map on normalized complexes, `∇ : N₁ → N₂`.

Option 3: the unnormalized `shuffleMap` conjugated by the Dold–Kan inclusion `N₁ ↪ F₁` and the
retraction `F₂ ↠ N₂`, so it is levelwise-concrete. -/
noncomputable def normalizedShuffleMap : N₁.obj X ⟶ N₂.obj X :=
  inclusionN₁ X ≫ shuffleMap X ≫ retractionN₂ X

/-- The Alexander–Whitney map on normalized complexes, `AW : N₂ → N₁`.

Option 3: the unnormalized `alexanderWhitney` conjugated by the Dold–Kan inclusion `N₂ ↪ F₂` and the
retraction `F₁ ↠ N₁`, so it is levelwise-concrete. -/
noncomputable def normalizedAlexanderWhitney : N₂.obj X ⟶ N₁.obj X :=
  inclusionN₂ X ≫ alexanderWhitney X ≫ retractionN₁ X

end BisimplicialObject

end CategoryTheory
