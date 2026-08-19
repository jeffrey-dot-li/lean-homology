import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.Presheaf

/-!
# Infinity Categories — Chapter 1

Experiments and formalizations accompanying Chapter 1 of Markus Land's
*Introduction to Infinity-Categories*.

The main objects used here are:

* `CategoryTheory.SimplicialObject C`, the category of simplicial objects in `C`;
* `SSet`, the category of simplicial sets;
* `SimplexCategory`, Mathlib's skeletal model of the simplex category `Δ`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe w v u

namespace HomologyLean.InfinityCategories.Ch1

variable {C : Type u} [Category.{v} C]

-- Definition 1.1.1: the simplex category and its coface and codegeneracy maps.
#print SimplexCategory
#print SimplexCategory.δ
#print SimplexCategory.σ

/-- A presheaf on `C` is a contravariant functor from `C` to types. -/
abbrev Presheaf (C : Type u) [Category.{v} C] :=
  Cᵒᵖ ⥤ Type w

#print Presheaf

-- Definition 1.1.6 Yoneda Embedding
example (C : Type u) [Category.{v} C] : C ⥤ Presheaf C := CategoryTheory.yoneda



-- Definition 1.1.7
#print SSet


-- Lemma 1.1.10: Yoneda Lemma
#check CategoryTheory.yonedaLemma


-- Lemma 1.1.11 Yoneda fully faithful
#check CategoryTheory.Yoneda.fullyFaithful


-- Corollary 1.1.12
#check SSet.yonedaEquiv
-- lemma SSet.yonedaEquiv  (C : Type u) [Category.{v} C] (X : SSet.{u})  :
--   X.obj (Opposite.op (SimplexCategory.mk n))



/--
Lemma 1.1.21: if `C` has limits and colimits of shape `I`, then the colimit
functor is left adjoint to the constant diagram functor, and the limit functor
is right adjoint to it.
-/
lemma limitColimitAdjunction (I : Type w) [Category.{w} I]
    [HasLimitsOfShape I C] [HasColimitsOfShape I C] :
    Nonempty (colim (J := I) (C := C) ⊣ Functor.const I) ∧
      Nonempty (Functor.const I ⊣ lim (J := I) (C := C)) := by
  sorry



/--
Lemma 1.1.22: an adjunction `F ⊣ G` induces an adjunction between the
corresponding post-composition functors on `I`-shaped diagrams.
-/
lemma adjunctionPostCompose (I : Type w) (C D : Type u)
    [Category.{v} C] [Category.{v} D] [Category.{w} I]
    (F : C ⥤ D) (G : D ⥤ C) (adj : Nonempty (F ⊣ G)) :
    Nonempty
      ((Functor.whiskeringRight I C D).obj F ⊣
        (Functor.whiskeringRight I D C).obj G) := by
  obtain ⟨adj⟩ := adj
  exact ⟨adj.whiskerRight I⟩

def representableDiagram (F : Presheaf C) :
    CostructuredArrow yoneda F ⥤ Presheaf C :=
  CostructuredArrow.proj yoneda F ⋙ yoneda


-- Lemma 1.1.26: Every presheaf is a colimit of representables.
def presheafIsColimitOfRepresentables (C : Type u) [Category.{v} C]
  (F : Presheaf C) : IsColimit ({
      pt := F
      ι := {
        app X := X.hom
        naturality := fun X Y f => f.w
      }
    } : Cocone (representableDiagram F)) :=
  CategoryTheory.Presheaf.isColimitTautologicalCocone F


end HomologyLean.InfinityCategories.Ch1
