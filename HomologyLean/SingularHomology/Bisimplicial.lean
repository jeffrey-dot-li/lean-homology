import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.CategoryTheory.Preadditive.FunctorCategory

open AlgebraicTopology CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type*} [Category* C]

variable (C) in
abbrev BisimplicialObject := SimplicialObject (SimplicialObject C)

namespace BisimplicialObject

@[simps!]
def diag : BisimplicialObject C ⥤ SimplicialObject C :=
  Functor.uncurry ⋙ (Functor.whiskeringLeft _ _ _).obj (Functor.diag _)

variable [Preadditive C] [HasFiniteCoproducts C]

-- SimplicialObject is a `def` (not `abbrev`), so typeclass search doesn't
-- unfold it to `Functor SimplexCategoryᵒᵖ C` to find functorCategoryPreadditive.
instance : Preadditive (SimplicialObject C) := CategoryTheory.functorCategoryPreadditive

instance : (alternatingFaceMapComplex C).Additive := { }

open ComplexShape in
instance (K : ChainComplex (ChainComplex C ℕ) ℕ) :
    HomologicalComplex₂.HasTotal K (.down ℕ) := by
  intro n
  let f (pq : ((down ℕ).π (down ℕ) (down ℕ) ⁻¹' {n})) : Fin (n + 1) × Fin (n + 1) :=
    ⟨⟨pq.1.1, by
      have := pq.2
      simp only [Set.mem_preimage, π_def, Set.mem_singleton_iff] at this
      lia⟩, ⟨pq.1.2, by
      have := pq.2
      simp only [Set.mem_preimage, π_def, Set.mem_singleton_iff] at this
      lia⟩⟩
  have := Finite.of_injective f (fun _ _ ↦ by grind)
  infer_instance

noncomputable abbrev F₁ : BisimplicialObject C ⥤ ChainComplex C ℕ :=
  alternatingFaceMapComplex _  ⋙
    (alternatingFaceMapComplex C).mapHomologicalComplex _ ⋙
      HomologicalComplex₂.totalFunctor _ _ _ _

abbrev F₂ : BisimplicialObject C ⥤ ChainComplex C ℕ :=
  diag ⋙ alternatingFaceMapComplex C

-- `hom`, `inv`, `homotopyHomInvId`, and `homotopyInvHomId` must also be natural in `X`
def eilenbergZilber (X : BisimplicialObject C) :
    HomotopyEquiv (F₁.obj X) (F₂.obj X) := sorry

variable [Preadditive C]

end BisimplicialObject

end CategoryTheory
