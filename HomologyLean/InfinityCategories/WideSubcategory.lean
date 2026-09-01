import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.MorphismProperty.Factorization
import Mathlib.CategoryTheory.EpiMono

/-!
# Wide subcategories

A wide subcategory of a category `A`, represented by the morphisms that belong to
it. Because it is wide, it has every object of `A`; closure under identities and
composition is therefore enough to specify its category structure.

These are the raw ingredients for the two wide subcategories `A⁺` and `A⁻` of an
Eilenberg–Zilber category (see `EilenbergZilberCategory`) and a generalized Reedy
category (see `GeneralizedReedyCategory`).
-/

open CategoryTheory

universe v u

namespace HomologyLean.InfinityCategories

/--
A wide subcategory of `A`, represented by the morphisms that belong to it.

Because it is wide, it has every object of `A`; closure under identities and
composition is therefore enough to specify its category structure.
-/
structure WideSubcategory (A : Type u) [Category.{v} A] where
  /-- The morphisms belonging to the wide subcategory. -/
  hom : MorphismProperty A
  /-- Every identity morphism belongs to the wide subcategory. -/
  id_mem : ∀ X : A, hom (𝟙 X)
  /-- The composite of two morphisms in the wide subcategory also belongs to it. -/
  comp_mem :
    ∀ {X Y Z : A} {f : X ⟶ Y} {g : Y ⟶ Z},
      hom f → hom g → hom (f ≫ g)

/-- The inverse image of a wide subcategory under a functor. -/
def WideSubcategory.inverseImage {A : Type u} {B : Type*}
    [Category.{v} A] [Category B] (W : WideSubcategory A) (F : B ⥤ A) :
    WideSubcategory B where
  hom := W.hom.inverseImage F
  id_mem := fun X ↦ by
    simpa using W.id_mem (F.obj X)
  comp_mem := fun hf hg ↦ by
    simpa using W.comp_mem hf hg

abbrev splitEpimorphisms (A : Type u) [Category.{v} A] :
    MorphismProperty A :=
  fun _ _ f => IsSplitEpi f

end HomologyLean.InfinityCategories
