import HomologyLean.InfinityCategories.WideSubcategory

/-!
# Generalized Reedy categories

This file introduces the notion of a (Berger–Moerdijk) generalized Reedy category,
following nLab, *generalized Reedy category*
(`https://ncatlab.org/nlab/show/generalized+Reedy+category`) and Berger–Moerdijk,
*On an extension of the notion of Reedy category* (2011).

Ordinary Reedy categories cannot contain non-identity isomorphisms. A generalized
Reedy category lifts this restriction, while retaining a factorization of every map
into a degree-lowering part followed by a degree-raising part, unique up to a unique
isomorphism, and hence the existence of a Reedy model structure on the category of
presheaves.

The related notion of an Eilenberg–Zilber category is the Cisinski variant: it
strengthens the last axiom below by requiring maps in `R⁻` to be split
epimorphisms that are determined by their sections.

This file also introduces `OrdinaryReedyCategory`, the original (strict) notion
due to Reedy, which strengthens a generalized Reedy category by requiring that
every isomorphism is induced by an equality of objects (no nontrivial
automorphisms). See the Reedy hierarchy in `.claude/plans/cubical-sites-gr-ez.md`.
-/

open CategoryTheory

universe w v u

namespace HomologyLean.InfinityCategories

/--
A (Berger–Moerdijk) generalized Reedy category: a category `R` with two wide
subcategories `R⁺` and `R⁻` and a degree function `degree : R → ι` into a linear
order `ι`.

The axioms state that non-isomorphisms in `R⁺` raise the degree, non-isomorphisms
in `R⁻` lower it, isomorphisms preserve it and belong to both wide subcategories,
every map factors through `R⁻` followed by `R⁺` uniquely up to a unique isomorphism,
and isomorphisms see the maps in `R⁻` as epimorphisms.
-/
class GeneralizedReedyCategory (R : Type u) [Category.{v} R]
    (ι : outParam (Type w)) [LinearOrder ι] [WellFoundedLT ι] where
  /-- The degree-raising wide subcategory `R⁺`. -/
  plus : WideSubcategory R
  /-- The degree-lowering wide subcategory `R⁻`. -/
  minus : WideSubcategory R
  /-- The degree of an object. -/
  degree : R → ι
  /-- Non-isomorphisms in `R⁺` raise the degree. -/
  degree_lt_of_plus {X Y : R} (f : X ⟶ Y) (hf : plus.hom f)
      (hf_noniso : ¬ IsIso f) :
    degree X < degree Y
  /-- Non-isomorphisms in `R⁻` lower the degree. -/
  degree_lt_of_minus {X Y : R} (f : X ⟶ Y) (hf : minus.hom f)
      (hf_noniso : ¬ IsIso f) :
    degree Y < degree X
  /-- Isomorphisms preserve the degree. -/
  degree_eq_of_isIso {X Y : R} (f : X ⟶ Y) (hf : IsIso f) :
    degree X = degree Y
  /-- Every isomorphism belongs to `R⁺`. -/
  isomorphisms_le_plus : MorphismProperty.isomorphisms R ≤ plus.hom
  /-- Every isomorphism belongs to `R⁻`. -/
  isomorphisms_le_minus : MorphismProperty.isomorphisms R ≤ minus.hom
  /-- Factorization of every map as a map in `R⁻` followed by a map in `R⁺`. -/
  factorization : MorphismProperty.HasFactorization minus.hom plus.hom
  /-- The factorization is unique up to a unique isomorphism. -/
  factorization_unique {X Y : R} (f : X ⟶ Y)
      (F G : MorphismProperty.MapFactorizationData minus.hom plus.hom f) :
    ∃! e : F.Z ≅ G.Z,
      F.i ≫ e.hom = G.i ∧ e.hom ≫ G.p = F.p
  /--
  (Berger–Moerdijk condition) Every isomorphism `θ` with `f ≫ θ = f` for a map
  `f` in `R⁻` is the identity: isomorphisms see the maps in `R⁻` as epimorphisms.
  -/
  iso_eq_id_of_comp_minus {X Y : R} (f : X ⟶ Y) (hf : minus.hom f)
      (θ : Y ⟶ Y) (hθ : IsIso θ) (h : f ≫ θ = f) :
    θ = 𝟙 Y

/--
An ordinary (strict) Reedy category: a generalized Reedy category with no
nontrivial isomorphisms. This is the original notion due to Reedy, where the
only isomorphisms are the identities (forced by `isIso_eqToHom`).

Ordinary Reedy categories are the left column of the Reedy hierarchy; they are
generalized Reedy categories in which the isomorphism condition is strengthened
to skeletality.
-/
class OrdinaryReedyCategory (R : Type u) [Category.{v} R]
    (ι : outParam (Type w)) [LinearOrder ι] [WellFoundedLT ι]
    extends GeneralizedReedyCategory R ι where
  /-- Every isomorphism is induced by an equality of objects; in particular,
  there are no nontrivial automorphisms. -/
  isIso_eqToHom {X Y : R} (f : X ⟶ Y) (hf : IsIso f) :
    ∃ h : X = Y, f = eqToHom h

/-!
## The category of Reedy categories

We can organize Reedy categories into a category whose objects are Reedy
categories and whose morphisms are structure-preserving functors. A functor
`F : R ⥤ S` between Reedy categories is **Reedy** if it preserves the two wide
subcategories and the degree:

- `F` maps `R⁺` into `S⁺` and `R⁻` into `S⁻`;
- `F` preserves degree: `degree (F.obj X) = degree X`.

The category `ReedyCat` has objects Reedy categories and morphisms Reedy
functors. The canonical forgetful functor `OrdinaryReedyCat ⥤ ReedyCat` is the
inclusion of the full subcategory of strict Reedy categories.
-/

/-- A Reedy functor: a functor between Reedy categories that preserves the
degree-raising and degree-lowering subcategories and the degree function. -/
structure ReedyFunctor (R S : Type u) [Category.{v} R] [Category.{v} S]
    (ι : outParam (Type w)) [LinearOrder ι] [WellFoundedLT ι]
    [GeneralizedReedyCategory R ι] [GeneralizedReedyCategory S ι] where
  /-- The underlying functor. -/
  toFunctor : R ⥤ S
  /-- The functor maps `R⁺` into `S⁺`. -/
  map_plus : ∀ {X Y : R} (f : X ⟶ Y), GeneralizedReedyCategory.plus.hom f →
    GeneralizedReedyCategory.plus.hom (toFunctor.map f)
  /-- The functor maps `R⁻` into `S⁻`. -/
  map_minus : ∀ {X Y : R} (f : X ⟶ Y), GeneralizedReedyCategory.minus.hom f →
    GeneralizedReedyCategory.minus.hom (toFunctor.map f)
  /-- The functor preserves degree. -/
  map_degree : ∀ X : R, GeneralizedReedyCategory.degree (toFunctor.obj X) =
    GeneralizedReedyCategory.degree X

/-- The category of generalized Reedy categories and Reedy functors. -/
structure ReedyCat (ι : Type w) [LinearOrder ι] [WellFoundedLT ι] where
  /-- Construct a Reedy category from a category with a Reedy structure. -/
  of ::
  /-- The underlying category. -/
  carrier : Type u
  /-- The category structure. -/
  [inst : Category.{v} carrier]
  /-- The Reedy structure. -/
  [reedy : GeneralizedReedyCategory carrier ι]

attribute [instance] ReedyCat.inst ReedyCat.reedy

namespace ReedyCat

variable {ι : Type w} [LinearOrder ι] [WellFoundedLT ι]

instance : CoeSort (ReedyCat ι) (Type u) :=
  ⟨ReedyCat.carrier⟩

/-- The type of morphisms in `ReedyCat`. -/
@[ext]
structure Hom (R S : ReedyCat ι) where
  /-- The underlying Reedy functor. -/
  toReedyFunctor : ReedyFunctor R.carrier S.carrier ι

instance : Category (ReedyCat ι) where
  Hom R S := Hom R S
  id R := ⟨⟨𝟭 R.carrier, fun _ hf => hf, fun _ hf => hf, fun _ => rfl⟩⟩
  comp F G := ⟨⟨F.toReedyFunctor.toFunctor ⋙ G.toReedyFunctor.toFunctor,
    fun _ hf => G.toReedyFunctor.map_plus _ (F.toReedyFunctor.map_plus _ hf),
    fun _ hf => G.toReedyFunctor.map_minus _ (F.toReedyFunctor.map_minus _ hf),
    fun X => (G.toReedyFunctor.map_degree (F.toReedyFunctor.toFunctor.obj X)).trans
      (F.toReedyFunctor.map_degree X)⟩⟩

end ReedyCat

/-- The category of ordinary (strict) Reedy categories and Reedy functors. -/
structure OrdinaryReedyCat (ι : Type w) [LinearOrder ι] [WellFoundedLT ι] where
  /-- Construct an ordinary Reedy category from a category with a strict Reedy structure. -/
  of ::
  /-- The underlying category. -/
  carrier : Type u
  /-- The category structure. -/
  [inst : Category.{v} carrier]
  /-- The strict Reedy structure. -/
  [ordinary : OrdinaryReedyCategory carrier ι]

attribute [instance] OrdinaryReedyCat.inst OrdinaryReedyCat.ordinary

namespace OrdinaryReedyCat

variable {ι : Type w} [LinearOrder ι] [WellFoundedLT ι]

instance : CoeSort (OrdinaryReedyCat ι) (Type u) :=
  ⟨OrdinaryReedyCat.carrier⟩

/-- The type of morphisms in `OrdinaryReedyCat`. -/
@[ext]
structure Hom (R S : OrdinaryReedyCat ι) where
  /-- The underlying Reedy functor. -/
  toReedyFunctor : ReedyFunctor R.carrier S.carrier ι

instance : Category (OrdinaryReedyCat ι) where
  Hom R S := Hom R S
  id R := ⟨⟨𝟭 R.carrier, fun _ hf => hf, fun _ hf => hf, fun _ => rfl⟩⟩
  comp F G := ⟨⟨F.toReedyFunctor.toFunctor ⋙ G.toReedyFunctor.toFunctor,
    fun _ hf => G.toReedyFunctor.map_plus _ (F.toReedyFunctor.map_plus _ hf),
    fun _ hf => G.toReedyFunctor.map_minus _ (F.toReedyFunctor.map_minus _ hf),
    fun X => (G.toReedyFunctor.map_degree (F.toReedyFunctor.toFunctor.obj X)).trans
      (F.toReedyFunctor.map_degree X)⟩⟩

/-- The canonical forgetful functor from ordinary Reedy categories to generalized
Reedy categories: the inclusion of the full subcategory of strict Reedy
categories. -/
def forgetful : OrdinaryReedyCat ι ⥤ ReedyCat ι where
  obj R := ReedyCat.of R.carrier
  map F := ⟨F.toReedyFunctor⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end OrdinaryReedyCat

namespace GeneralizedReedyCategory

variable {R : Type u} [Category.{v} R] {ι : Type w} [LinearOrder ι] [WellFoundedLT ι]
    [GeneralizedReedyCategory R ι]

/-- A morphism belongs to the positive wide subcategory `R⁺`. -/
abbrev IsPlus {X Y : R} (f : X ⟶ Y) : Prop :=
  GeneralizedReedyCategory.plus.hom f

/-- A morphism belongs to the negative wide subcategory `R⁻`. -/
abbrev IsMinus {X Y : R} (f : X ⟶ Y) : Prop :=
  GeneralizedReedyCategory.minus.hom f

end GeneralizedReedyCategory

end HomologyLean.InfinityCategories
