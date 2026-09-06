import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Absolute limits and colimits

An **absolute limit** (resp. **absolute colimit**) is a limit (resp. colimit)
that is preserved by every functor out of the ambient category. These are the
limits/colimits that exist "for free" — they are preserved by all functors, not
just the continuous/cocontinuous ones.

The main examples are:
- **Absolute pushouts**: pushouts preserved by every functor. These are the key
  condition for Campion's Eilenberg–Zilber categories (every pair of `R⁻` maps
  with common domain has an absolute pushout).
- **Absolute pullbacks**: pullbacks preserved by every functor.

## References

- Campion, *Cubical sites as Eilenberg–Zilber categories* (arXiv:2303.06206),
  Def 2.1 and Lemma 2.2.
- Bergner–Rezk, *Reedy categories and the Θ-construction* (2013), §4.
-/

open CategoryTheory Limits

universe w v u

namespace HomologyLean.InfinityCategories

/--
An absolute pushout: a pushout square that is preserved by every functor out of
the ambient category. Equivalently, the pushout cocone is a colimit in every
image category.

This is the key condition for Campion's Eilenberg–Zilber categories: every pair
of `R⁻` maps with common domain has an absolute pushout.
-/
def IsAbsolutePushout {C : Type u} [Category.{v} C] {Z X Y P : C}
    (f : Z ⟶ X) (g : Z ⟶ Y) (inl : X ⟶ P) (inr : Y ⟶ P) : Prop :=
  IsPushout f g inl inr ∧
  ∀ {D : Type u} [Category.{v} D] (F : C ⥤ D),
    IsPushout (F.map f) (F.map g) (F.map inl) (F.map inr)

/--
An absolute pullback: a pullback square that is preserved by every functor out
of the ambient category.
-/
def IsAbsolutePullback {C : Type u} [Category.{v} C] {P X Y Z : C}
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z) : Prop :=
  IsPullback fst snd f g ∧
  ∀ {D : Type u} [Category.{v} D] (F : C ⥤ D),
    IsPullback (F.map fst) (F.map snd) (F.map f) (F.map g)

end HomologyLean.InfinityCategories
