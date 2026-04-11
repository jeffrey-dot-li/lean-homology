/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Functor.Hom
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# Working file for categorical constructions

Kernel/cokernel functors, smash product, lifting properties.
-/

open CategoryTheory
open CategoryTheory.Limits

universe v u

variable {C D : Type u} [Category.{v} C]

section KernelCokernel
variable [Category.{v} D]
  [HasZeroObject C] [HasFiniteLimits C] [HasFiniteColimits C]
attribute [local instance] HasZeroObject.zeroMorphismsOfZeroObject

/-- The kernel as a functor `Arrow C ⥤ C`, sending an arrow `f` to `ker f`. -/
noncomputable def ker : Arrow C ⥤ C where
  obj f := pullback f.hom ((isZero_zero C).to_ f.right)
  map {f f' } m  := by
    simp only [Functor.id_obj]
    refine pullback.lift ?_ ?_ ?_
    · exact (pullback.fst f.hom _) ≫ m.left
    · refine (pullback.snd f.hom _) ≫ 0
    · simp [pullback.condition_assoc, zero_of_from_zero]
  map_id f := by
    apply pullback.hom_ext <;> simp [zero_of_to_zero]
  map_comp {X Y Z} (f g) := by
    apply pullback.hom_ext <;> simp [zero_of_to_zero]

/-- The cokernel as a functor `Arrow C ⥤ C`, sending an arrow `f` to `coker f`. -/
noncomputable def coker : Arrow C ⥤ C where
  obj f := pushout f.hom ((isZero_zero C).from_ f.left)
  map {f f'} m := by
    simp only [Functor.id_obj]
    refine pushout.desc ?_ ?_ ?_
    · exact m.right ≫ (pushout.inl f'.hom _)
    · refine 0 ≫ (pushout.inr f'.hom _)
    · simp only [ zero_comp, comp_zero]
      obtain m_w_assoc := m.w_assoc
      simp only [Functor.id_obj, Functor.id_map] at m_w_assoc
      rw [←m_w_assoc, pushout.condition]
      simp [zero_of_from_zero]
  map_id f := by
    apply pushout.hom_ext <;> simp [zero_of_from_zero]
  map_comp {X Y Z} (f g) := by
    apply pushout.hom_ext <;> simp [zero_of_from_zero]

/-- `coprodToProd` as a bifunctor `C × C ⥤ Arrow C`, sending `(A, B)` to the arrow
`coprodToProd A B : A ⨿ B ⟶ A ⨯ B`. -/
noncomputable def coprodToProd : C × C ⥤ Arrow C where
  obj AB := Arrow.mk (coprod.desc (prod.lift (𝟙 AB.1) 0) (prod.lift 0 (𝟙 AB.2)))
  map {AB AB'} fg := Arrow.homMk (coprod.map fg.1 fg.2) (prod.map fg.1 fg.2) (by
    simp only [Arrow.mk_left, Arrow.mk_right]
    ext <;> simp)
  map_id AB := by
    ext <;> simp [Arrow.homMk]
  map_comp {AB AB' AB''} fg fg' := by
    ext <;> simp [Arrow.homMk]

@[simp] lemma coprodToProd_obj_left (A B : C) :
    (coprodToProd.obj (A, B)).left = Limits.coprod A B := rfl

@[simp] lemma coprodToProd_obj_right (A B : C) :
    (coprodToProd.obj (A, B)).right = Limits.prod A B := rfl

/-- The smash product with a fixed object `A`, as a functor `C ⥤ C` sending `B ↦ A ∧ B`. -/
noncomputable def smashProductFunctor : C × C ⥤ C := coprodToProd ⋙ coker

/-- The coproduct-smash functor: `(A, B, C) ↦ (A ∧ B) ⨿ C`.
Defined as the composition: project `(A,B)` and `C`, smash the first pair, then coproduct. -/
noncomputable def coprodSmash : C × C × C ⥤ C :=
  Functor.prod'
    (Functor.prod' (CategoryTheory.Prod.fst C (C × C))
      (CategoryTheory.Prod.snd C (C × C) ⋙ CategoryTheory.Prod.fst C C)
      ⋙ smashProductFunctor)
    (CategoryTheory.Prod.snd C (C × C) ⋙ CategoryTheory.Prod.snd C C)
  ⋙ CategoryTheory.Functor.uncurry.obj coprod.functor

/-- The smash-coproduct functor: `(A, B, C) ↦ A ⨿ (B ∧ C)`.
Defined as the composition: project `A` and `(B,C)`, smash the second pair, then coproduct. -/
noncomputable def smashCoprod : C × C × C ⥤ C :=
  Functor.prod'
    (CategoryTheory.Prod.fst C (C × C))
    (CategoryTheory.Prod.snd C (C × C) ⋙ smashProductFunctor)
  ⋙ CategoryTheory.Functor.uncurry.obj coprod.functor

/-- The canonical natural isomorphism `(A ∧ B) ⨿ C ≅ A ⨿ (B ∧ C)`. -/
noncomputable def coprodSmashIso : coprodSmash ≅ (smashCoprod : C × C × C ⥤ C) := sorry

/-- The product-smash functor: `(A, B, C) ↦ (A ∧ B) ⨯ C`.
Defined as the composition: project `(A,B)` and `C`, smash the first pair, then product. -/
noncomputable def prodSmash : C × C × C ⥤ C :=
  Functor.prod'
    (Functor.prod' (CategoryTheory.Prod.fst C (C × C))
      (CategoryTheory.Prod.snd C (C × C) ⋙ CategoryTheory.Prod.fst C C)
      ⋙ smashProductFunctor)
    (CategoryTheory.Prod.snd C (C × C) ⋙ CategoryTheory.Prod.snd C C)
  ⋙ CategoryTheory.Functor.uncurry.obj prod.functor

/-- The smash-product functor: `(A, B, C) ↦ A ⨯ (B ∧ C)`.
Defined as the composition: project `A` and `(B,C)`, smash the second pair, then product. -/
noncomputable def smashProd : C × C × C ⥤ C :=
  Functor.prod'
    (CategoryTheory.Prod.fst C (C × C))
    (CategoryTheory.Prod.snd C (C × C) ⋙ smashProductFunctor)
  ⋙ CategoryTheory.Functor.uncurry.obj prod.functor

/-- The canonical natural isomorphism `(A ∧ B) ⨯ C ≅ A ⨯ (B ∧ C)`. -/
noncomputable def prodSmashIso : prodSmash ≅ (smashProd : C × C × C ⥤ C) := sorry

/-- The `coprodToProd` arrow applied after smashing the first pair:
`(A, B, C) ↦ ((A ∧ B) ⨿ C ⟶ (A ∧ B) ⨯ C)`. -/
noncomputable def coprodToProdSmashLeft : C × C × C ⥤ Arrow C :=
  Functor.prod'
    (Functor.prod' (CategoryTheory.Prod.fst C (C × C))
      (CategoryTheory.Prod.snd C (C × C) ⋙ CategoryTheory.Prod.fst C C)
      ⋙ smashProductFunctor)
    (CategoryTheory.Prod.snd C (C × C) ⋙ CategoryTheory.Prod.snd C C)
  ⋙ coprodToProd

/-- The `coprodToProd` arrow applied after smashing the second pair:
`(A, B, C) ↦ (A ⨿ (B ∧ C) ⟶ A ⨯ (B ∧ C))`. -/
noncomputable def coprodToProdSmashRight : C × C × C ⥤ Arrow C :=
  Functor.prod'
    (CategoryTheory.Prod.fst C (C × C))
    (CategoryTheory.Prod.snd C (C × C) ⋙ smashProductFunctor)
  ⋙ coprodToProd

/-- The square
```
  (A ∧ B) ⨿ C  ──coprodToProd──▸  (A ∧ B) ⨯ C
       │                                │
  coprodSmashIso                   prodSmashIso
       │                                │
       ▾                                ▾
  A ⨿ (B ∧ C)  ──coprodToProd──▸  A ⨯ (B ∧ C)
```
commutes naturally in `(A, B, C)`. -/
noncomputable def coprodToProd_square :
    coprodToProdSmashLeft ≅ (coprodToProdSmashRight : C × C × C ⥤ Arrow C) := sorry

section SmashProduct

open MonoidalCategory ZeroObject

/-- The smash product monoidal structure on `C`: the tensor is the smash product
`coker(A ⨿ B ⟶ A ⨯ B)` and the unit is the zero object. -/
noncomputable instance smashMonoidal : MonoidalCategory C where
  tensorObj A B := smashProductFunctor.obj (A, B)
  whiskerLeft X _ _ f := smashProductFunctor.map ((𝟙 X), f)
  whiskerRight f Y := smashProductFunctor.map (f, (𝟙 Y))
  tensorHom f g := smashProductFunctor.map (f, g)
  tensorUnit := sorry
  associator X Y Z := {
    hom := by
      unfold smashProductFunctor
      simp only [Functor.comp_obj]
      unfold _root_.coker
      simp only [Functor.id_obj, id_eq]
      generalize_proofs isZero
      refine pushout.desc ?_ 0 ?_
      ·
        simp only [coprodToProd_obj_left, coprodToProd_obj_right]
        refine ?_ ≫ pushout.inl _ _
        have m := (prodSmashIso.hom.app (X, Y, Z))
        simp only [prodSmash, smashProductFunctor, _root_.coker, Functor.id_obj, zero_comp, id_eq,
          Functor.comp_obj, Functor.prod'_obj, Prod.fst_obj, Prod.snd_obj, coprodToProd_obj_left,
          coprodToProd_obj_right, Functor.uncurry_obj_obj, prod.functor_obj_obj, smashProd] at m
        exact m
      · sorry
    inv := sorry
    hom_inv_id := sorry
    inv_hom_id := sorry
  }

  leftUnitor X := sorry
  rightUnitor X := sorry
  tensorHom_def := sorry
  id_tensorHom_id := sorry
  tensorHom_comp_tensorHom := sorry
  whiskerLeft_id := sorry
  id_whiskerRight := sorry
  associator_naturality := sorry
  leftUnitor_naturality := sorry
  rightUnitor_naturality := sorry
  pentagon := sorry
  triangle := sorry

end SmashProduct

end KernelCokernel


section Fibration

variable {E B V W : C} (p : E ⟶ B) (i : V ⟶ W)

/-- The right lifting property of `p` with respect to `i`: given `f : V ⟶ E` and `f̄ : W ⟶ B`
with `i ≫ f̄ = f ≫ p`, there exists a lift `f̃ : W ⟶ E` making both triangles commute. -/
structure HasLift (f : V ⟶ E) (fbar : W ⟶ B) (sq : i ≫ fbar = f ≫ p) where
  lift : W ⟶ E
  fac_left : i ≫ lift = f
  fac_right : lift ≫ p = fbar

/-- `i` has the left lifting property against `p` if every commutative square admits a
diagonal filler. Equivalently, `p` has the right lifting property against `i`. -/
def HasLLP : Prop :=
  ∀ (f : V ⟶ E) (fbar : W ⟶ B) (sq : i ≫ fbar = f ≫ p), Nonempty (HasLift p i f fbar sq)

notation:50 i " ⊥ " p => HasLLP p i

namespace MorphismProperty

/-- The left orthogonal complement: all morphisms having LLP against every morphism in `T`. -/
def llp (T : MorphismProperty C) : MorphismProperty C :=
  fun _ _ i => ∀ ⦃E B : C⦄ (p : E ⟶ B), T p → i ⊥ p

/-- The right orthogonal complement: all morphisms having RLP against every morphism in `T`. -/
def rlp (T : MorphismProperty C) : MorphismProperty C :=
  fun _ _ p => ∀ ⦃V W : C⦄ (i : V ⟶ W), T i → i ⊥ p

end MorphismProperty

/-- The pullback of a map with the RLP against `i` also has the RLP against `i`.
Given `i ⊥ p` and any `g : X ⟶ B`, we have `i ⊥ pullback.fst g p`. -/
lemma pullback_HasRLP {X : C} (g : X ⟶ B) (h : i ⊥ p) [HasPullback g p] :
    i ⊥ (pullback.fst g p) := by
  intro f fbar sq
  -- f : V ⟶ pullback g p, fbar : W ⟶ X, sq : i ≫ fbar = f ≫ pullback.fst g p
  -- Build the outer square against p using the pullback condition
  have outer_sq : i ≫ (fbar ≫ g) = (f ≫ pullback.snd g p) ≫ p := by
    simp only [Category.assoc]
    rw [reassoc_of% sq]
    congr 1
    simp only [pullback.condition]
  obtain ⟨l⟩ := h (f ≫ pullback.snd g p) (fbar ≫ g) outer_sq
  refine ⟨⟨pullback.lift fbar l.lift ?_, ?_, ?_⟩⟩
  · exact l.fac_right.symm
  · apply pullback.hom_ext
    · simp [ sq, Category.assoc]
    · simp [l.fac_left]
  · simp

/-- The pushout of a map with the LLP against `p` also has the LLP against `p`.
Given `i ⊥ p` and any `g : V ⟶ Y`, we have `pushout.inl g i ⊥ p`. -/
lemma pushout_HasLLP {Y : C} (g : V ⟶ Y) (h : i ⊥ p) [HasPushout g i] :
    (pushout.inl g i) ⊥ p := by
  intro f fbar sq
  -- f : Y ⟶ E, fbar : pushout g i ⟶ B, sq : pushout.inl g i ≫ fbar = f ≫ p
  -- Build the outer square: i ≫ (pushout.inr g i ≫ fbar) = (g ≫ f) ≫ p
  have outer_sq : i ≫ (pushout.inr g i ≫ fbar) = (g ≫ f) ≫ p := by
    rw [← Category.assoc, ← pushout.condition, Category.assoc, sq, Category.assoc]
  obtain ⟨l⟩ := h (g ≫ f) (pushout.inr g i ≫ fbar) outer_sq
  refine ⟨⟨pushout.desc f l.lift ?_, ?_, ?_⟩⟩
  · exact l.fac_left.symm
  · simp
  · apply pushout.hom_ext
    · simp [sq]
    · simp [l.fac_right]



/-- The RLP is closed under composition: if `i ⊥ p` and `i ⊥ p'`, then `i ⊥ (p' ≫ p)`. -/
lemma HasLLP_comp {E' : C} (p' : E' ⟶ E) (hp : i ⊥ p) (hp' : i ⊥ p') :
    i ⊥ (p' ≫ p) := by
  intro f fbar sq
  -- First, lift against p: the top map is f ≫ p' and the bottom map is fbar
  obtain ⟨mid, mid_left, mid_right⟩ :=
    (hp (f ≫ p') fbar (by simp only [Category.assoc, sq])).some
  -- Then, lift against p': the top map is f and the bottom map is mid
  obtain ⟨lift, lift_left, lift_right⟩ := (hp' f mid mid_left).some
  exact ⟨⟨lift, lift_left, by rw [reassoc_of% lift_right, mid_right]⟩⟩

/-- The RLP is closed under products: if `i ⊥ fb b` for every `b : β`, then
`i ⊥ Pi.map fb` where `Pi.map fb : ∏ᶜ Eb ⟶ ∏ᶜ Bb` is the product of the `fb b`. -/
lemma HasLLP_pi {β : Type*} {Eb Bb : β → C} (fb : (b : β) → Eb b ⟶ Bb b)
    [HasProduct Eb] [HasProduct Bb] (hfb : ∀ b, i ⊥ fb b) :
    i ⊥ (Limits.Pi.map fb) := by
  intro f fbar sq
  -- Project the square onto each component and lift there
  have lift_at := fun b =>
    (hfb b (f ≫ Pi.π Eb b) (fbar ≫ Pi.π Bb b)
      (by simp [reassoc_of% sq])).some
  -- Assemble the componentwise lifts into the product
  exact ⟨⟨Pi.lift fun b => (lift_at b).lift,
    Pi.hom_ext _ _ fun b => by simp [(lift_at b).fac_left],
    Pi.hom_ext _ _ fun b => by simp [(lift_at b).fac_right]⟩⟩


-- Need assumption about fibrancy, cannot prove independently
-- /-- If `i ⊥ p`, then `𝟙 Y ⨯ i ⊥ p` for any `Y`. -/
-- lemma HasLLP_prod_id {Y : C} [HasBinaryProduct Y V] [HasBinaryProduct Y W] (h : i ⊥ p) :
--     (prod.map (𝟙 Y) i) ⊥ p := by
--   intro f fbar sq
--   refine ⟨?_⟩
--   refine ⟨?_, ?_, ?_⟩
--   ·

section CartesianClosed

open MonoidalCategory CartesianMonoidalCategory

variable [CartesianMonoidalCategory C] [MonoidalClosed C]

/-- In a cartesian closed category, the internal hom out of `X` preserves binary products:
`(Y × Z)^X ≅ Y^X × Z^X`. -/
noncomputable def ihomProdIso (X Y Z : C) :
    (ihom X).obj (Y ⊗ Z) ≅ (ihom X).obj Y ⊗ (ihom X).obj Z := by
  haveI : PreservesLimitsOfSize.{0, 0} (ihom X) :=
    (ihom.adjunction X).rightAdjoint_preservesLimits
  exact prodComparisonIso (ihom X) Y Z




noncomputable def prodIhomIso (A X Y : C) :
  (ihom (Y ⊗ X)).obj (A) ≅ (ihom X).obj ((ihom Y).obj A)  := {
    hom := by
      refine ((ihom.adjunction _).homEquiv _ _).toFun ?_
      refine ((ihom.adjunction _).homEquiv _ _).toFun ?_
      simp only [curriedTensor_obj_obj]
      refine (α_ _ _ _).inv ≫ ?_
      refine ((ihom.adjunction _).homEquiv _ _).invFun ?_
      exact 𝟙 _
    inv := by
      refine ((ihom.adjunction _).homEquiv _ _).toFun ?_
      -- simp
      refine (α_ _ _ _).hom ≫ ?_
      refine ((ihom.adjunction _).homEquiv _ _).invFun ?_
      refine ((ihom.adjunction _).homEquiv _ _).invFun ?_
      exact 𝟙 _
    hom_inv_id := by

      simp_all only [curriedTensor_obj_obj, Equiv.invFun_as_coe, id_eq, Equiv.toFun_as_coe]
      sorry

  }


end CartesianClosed

end Fibration
