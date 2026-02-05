/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Coproducts in Categories

This file contains lemmas about coproducts in categories.

## Main results

* `eq_id_of_comp_ι_eq_ι`: If a morphism from a coproduct composes with every inclusion to give
  that inclusion, then it is the identity.
-/

open CategoryTheory
open CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

section Coproduct

variable {ι : Type*} {A B : C}

/--
If `B` is the coproduct of copies of `A` indexed by `ι`, and `f : B ⟶ B` is such that
for every inclusion morphism `s : A ⟶ B`, we have `s ≫ f = s`, then `f = 𝟙 B`.

This expresses that a morphism from a coproduct is uniquely determined by its action on
the inclusion morphisms, and if it fixes all inclusions, it must be the identity.
-/
lemma eq_id_of_comp_ι_eq_ι [HasCoproduct (fun (_ : ι) => A)]
    (f : ∐ (fun (_ : ι) => A) ⟶ ∐ (fun (_ : ι) => A))
    (h : ∀ (i : ι), Sigma.ι (fun (_ : ι) => A) i ≫ f = Sigma.ι (fun (_ : ι) => A) i) :
    f = 𝟙 (∐ (fun (_ : ι) => A)) := by
  ext i
  simp only [h]
  simp only [Category.comp_id]

end Coproduct
