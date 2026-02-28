/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 1e9b6cfb-adff-4460-9c43-a47b58a342e1

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma sub_tensorHom {C : Type*} [Category C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C]
    {W X Y Z : C} (f g : W ⟶ X) (h : Y ⟶ Z) :
    (f - g) ⊗ₘ h = f ⊗ₘ h - g ⊗ₘ h

- lemma tensorHom_sub {C : Type*} [Category C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C]
    {W X Y Z : C} (f : W ⟶ X) (g h : Y ⟶ Z) :
    f ⊗ₘ (g - h) = f ⊗ₘ g - f ⊗ₘ h
-/

/-
  Tensor distributes over subtraction in monoidal preadditive categories.

  - `sub_tensorHom`: `(f - g) ⊗ₘ h = f ⊗ₘ h - g ⊗ₘ h`
  - `tensorHom_sub`: `f ⊗ₘ (g - h) = f ⊗ₘ g - f ⊗ₘ h`
-/
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Preadditive.Basic


open CategoryTheory

open scoped MonoidalCategory

namespace HomologyLean.CategoryTheory

/-- In a monoidal preadditive category, tensor distributes over subtraction
on the left: `(f - g) ⊗ₘ h = f ⊗ₘ h - g ⊗ₘ h`. -/
lemma sub_tensorHom {C : Type*} [Category C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C]
    {W X Y Z : C} (f g : W ⟶ X) (h : Y ⟶ Z) :
    (f - g) ⊗ₘ h = f ⊗ₘ h - g ⊗ₘ h := by
  rw [sub_eq_add_neg]
  have h_fubini : ∀ (f g : W ⟶ X) (h : Y ⟶ Z), (f + g) ⊗ₘ h = f ⊗ₘ h + g ⊗ₘ h :=
    fun f g h => MonoidalPreadditive.add_tensor f g h
  rw [h_fubini, sub_eq_add_neg]
  suffices (-g) ⊗ₘ h + g ⊗ₘ h = 0 by
    rw [add_right_inj, (neg_eq_of_add_eq_zero_left this).symm]
  rw [← h_fubini (-g) g h, show (-g + g) = 0 from neg_add_cancel g, MonoidalPreadditive.zero_tensor]

/-- In a monoidal preadditive category, tensor distributes over subtraction
on the right: `f ⊗ₘ (g - h) = f ⊗ₘ g - f ⊗ₘ h`. -/
lemma tensorHom_sub {C : Type*} [Category C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C]
    {W X Y Z : C} (f : W ⟶ X) (g h : Y ⟶ Z) :
    f ⊗ₘ (g - h) = f ⊗ₘ g - f ⊗ₘ h := by
  rw [sub_eq_add_neg]
  have h_fubini : ∀ (f : W ⟶ X) (g h : Y ⟶ Z), f ⊗ₘ (g + h) = f ⊗ₘ g + f ⊗ₘ h :=
    fun f g h => MonoidalPreadditive.tensor_add f g h
  rw [h_fubini, sub_eq_add_neg]
  suffices f ⊗ₘ (-h) + f ⊗ₘ h = 0 by
    rw [add_right_inj, (neg_eq_of_add_eq_zero_left this).symm]
  rw [← h_fubini f (-h) h, neg_add_cancel, MonoidalPreadditive.tensor_zero]

end HomologyLean.CategoryTheory
