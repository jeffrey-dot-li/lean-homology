/-
  Additional simp lemmas for `biprod.map`.
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

variable {X Y X' Y' X'' Y'' : C}
  [HasBinaryBiproduct X Y] [HasBinaryBiproduct X' Y'] [HasBinaryBiproduct X'' Y'']

/-- `biprod.map` respects composition (componentwise). -/
@[simp]
lemma biprod.map_comp
    (f1 : X ⟶ X') (g1 : Y ⟶ Y')
    (f2 : X' ⟶ X'') (g2 : Y' ⟶ Y'') :
    biprod.map f1 g1 ≫ biprod.map f2 g2 = biprod.map (f1 ≫ f2) (g1 ≫ g2) := by
  apply biprod.hom_ext <;> simp [Category.assoc]

@[simp] lemma biprod.map_zero :
  biprod.map (0 : X ⟶ X') (0 : Y ⟶ Y') = 0 := by
  apply biprod.hom_ext <;> simp
